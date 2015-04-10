{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns, TupleSections #-}

module Core(
    Equal(..), sym,
    Goal(..), State(..),
    resetState, getState, getProofs, getGoals,
    defineFunction, defineData, addGoal,
    firstGoal, firstSubgoal, rewriteExp, applyProof,
    splitCase, splitCon, removeLam,
    withState, withSubgoal,
    ) where

import Control.Applicative
import Exp
import Util
import System.IO.Unsafe
import Data.IORef
import Data.Generics.Uniplate.Data
import Data.List.Extra
import Data.Data

data Reduced = Reduced | Unreduced deriving Eq

data Proved = Defined | Proved deriving Eq

data State = State
    {types :: [(String, [(Con,Int)])] -- these should go away
    ,proof :: [(Equal, Proved)]
    ,goals :: [Goal] -- none are literally equal
    }

data Equal = Exp :=: Exp deriving (Data,Typeable,Show,Eq)

data Goal = Goal Equal [(Equal, Reduced)] -- prove the ultimate goal, given a list of subgoals, where True ones have been reduced

sym :: Equal -> Equal
sym (a :=: b) = b :=: a

resetState :: IO ()
resetState = withState $ const $ State [] [] []

invalid :: String -> a
invalid x = error $ "Proof step is invalid, " ++ x

promote :: State -> State
promote s@State{goals = Goal t []:xs} = promote $ s{proof = proof s ++ [(t,Proved)], goals = xs}
promote s@State{goals = Goal t ((a :=: b, _):gs):xs} | a == b = promote $ s{goals = Goal t gs : xs}
promote s = s

instance Pretty Equal where
    pretty (a :=: b) = pretty a ++ " = " ++ pretty b

instance Pretty State where
    pretty State{..} = unlines $
        [unwords $ "data" : x : "=" : intercalate ["|"] [fromCon y : replicate n "_" | (y,n) <- ys] | (x,ys) <- types] ++
        ["\n" ++ pretty x ++ (if b == Defined then " -- defined" else "") | (x,b) <- proof] ++
        ["\n-- GOAL\n" ++ pretty a ++ concat
            ["\n-- SUBGOAL" ++ (if reduced == Reduced then " (reduced)" else "") ++ "\n" ++
             pretty a | (a, reduced) <- xs]
            | Goal a xs <- goals]


-- trusted Core operations:
-- * Reorder goals
-- * Apply transformations to an expression
--   * Based on proof, direct textually equivalent equality substitution
--   * Based on eval equivalence
-- * Split based on Case, Ctor (induces a reduction)
-- * Reorder or drop lambda parameters equally (positional quantifiers)
-- * Induction, direct textually equivalent equality substitution

addGoal :: Exp -> Exp -> IO Equal
addGoal a b = do
    withState $ \s -> s{goals = Goal (a :=: b) [(a :=: b, Unreduced)] : goals s}
    return $ a :=: b


-- | Make goal at position i the first goal
firstGoal :: Int -> IO ()
firstGoal i = withState $ \s ->
    let (pre,x:post) = splitAt i $ goals s
    in s{goals = x:pre++post}

-- | Make subgoal at position i the first subgoal
firstSubgoal :: Int -> IO ()
firstSubgoal i = withState $ \s@State{goals=Goal a bs:rest} ->
    let (pre,x:post) = splitAt i bs
    in s{goals = Goal a (x:pre++post) : rest}


-- | Define a new function
defineFunction :: String -> Exp -> IO Equal
defineFunction name body = do
    let prf = Var (V name) :=: body
    withState $ \s -> s{proof = proof s ++ [(prf, Defined)]}
    return prf

-- | Define a new data type, defines the case splitting rule.
defineData :: [(String,Int)] -> IO Equal
defineData ctrs = do
    withState $ \s -> s{proof = proof s ++ [(prf, Defined)]}
    return prf
    where
        v1:vs = fresh []
        prf = Lam v1 (Var v1) :=: Lam v1 (Case (Var v1) alts)
        alts = [(PCon (C a) vs', Con (C a) `apps` map Var vs') | (a,b) <- ctrs, let vs' = take b vs]


-- using the proof (which must be True, or inductively True) apply to produce this subgoal
applyProof :: Equal -> Equal -> IO ()
applyProof given@(from :=: to) new = withState $ \s ->
    if not $ valid s given then error $ "applyProof called with an invalid proof, " ++ show given else
        case goals s of
            Goal r1 ((x, reduced):r2):r3
                | transformBi (\x -> if x == from then to else x) x == new
                -> s{goals = Goal r1 ((new, reduced):r2) : r3}
    where
        valid s prf | prf `elem` map fst (proof s) = True
                    | sym prf `elem` map fst (proof s) = True
                    | Goal t ((_,Reduced):_):_ <- goals s, prf `elem` [t, sym t] = True
                    | otherwise = False


-- rewrite expressions, must be equivalent under eval
rewriteExp :: Equal -> IO ()
rewriteExp (a :=: b) = withSubgoal $ \(o@(x :=: y), reduced) ->
    if eval x == eval a && eval y == eval b then [(a :=: b,reduced)] else invalid "rewriteExp, not equal"


splitCase :: IO ()
splitCase = withSubgoal $ \(o@(a :=: b), reduced) ->
    if pattern a /= pattern b then invalid $ "splitCase on different patterns, " ++ pretty o
    else map (,reduced) $ zipWith (:=:) (split a) (split b)
    where
        -- distinguishes the salient features
        pattern (fromLams . relabel -> (vs, Case _ alts)) = (vs, map (patCon . fst) alts)
        pattern x = invalid $ "splitCase not on a case, " ++ pretty x

        split (fromLams -> (vs, Case on alts)) = lams vs on : [lams (vs ++ patVars p) x | (p,x) <- alts]


splitCon :: IO ()
splitCon = withSubgoal $ \(o@(a :=: b), _) ->
    if pattern a /= pattern b then invalid $ "splitCon on different patterns, " ++ pretty o
    else map (,Reduced) $ zipWith (:=:) (split a) (split b)
    where
        pattern (fromLams -> (vs, fromApps -> (Con ctr, args))) = (length vs, ctr, length args)
        pattern x = invalid $ "splitCon not a con, " ++ pretty x

        split (fromLams -> (vs, fromApps -> (Con ctr, args))) = map (lams vs) args


-- technically not necessary, just cleans up quantifiers
removeLam :: IO ()
removeLam = withSubgoal $ \((fromLams -> (as, a)) :=: (fromLams -> (bs, b)), reduced) ->
    let rem = f as a `intersect` f bs b
    in if null rem then invalid "removeLam, none are redundant" else [(g rem as a :=: g rem bs b, reduced)]
    where
        f as a = [i | let fr = free a, (i,x) <- zip [0..] as, x `notElem` fr]
        g rem as a = lams [x | (i,x) <- zip [0..] as, i `notElem` rem] a


{-# NOINLINE state #-}
state :: IORef State
state = unsafePerformIO $ newIORef $ State [] [] []

getState :: IO State
getState = readIORef state

getGoals = goals <$> getState
getProofs = map fst . proof <$> getState

withState :: (State -> State) -> IO ()
withState f = modifyIORef state (promote . f)

-- Nothing indicates you proved it
withGoal :: (Goal -> Goal) -> IO ()
withGoal f = withState $ \s@State{goals=g:gs} -> s{goals = f g : gs}

withSubgoal :: ((Equal, Reduced) -> [(Equal, Reduced)]) -> IO ()
withSubgoal f = withGoal $ \(Goal t (p:ps)) -> Goal t (f p ++ ps)
