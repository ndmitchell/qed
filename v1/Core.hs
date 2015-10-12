{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns, TupleSections #-}

module Core(
    Equal(..), sym,
    Goal(..), State(..),
    resetState, getState, getProofs, getGoals,
    defineFunction, defineData, addGoal,
    firstGoal, firstSubgoal, rewriteExp, applyProof,
    splitCase, splitCon, splitOther, removeLam,
    cheat
    ) where

import Control.Applicative
import Control.Exception
import Control.DeepSeq
import Exp
import Util
import System.IO.Unsafe
import Data.IORef
import Data.Generics.Uniplate.Data
import Data.List.Extra
import Data.Data

-- What inductive hypothesis is available to us
data Induction
    = Coinduction          -- can prove by coinduction, have generated a constructor and am at the root
    | InductionEq Int Int  -- position i in the original and j in the current are equal
    | InductionGt Int Int  -- position i in the original is strictly greater than j
      deriving (Show,Eq)

data Proved = Defined | Proved deriving (Show,Eq)

data State = State
    {types :: [(String, [(Con,Int)])] -- these should go away
    ,proved :: [(Equal, Proved)]
    ,goals :: [Goal] -- none are literally equal
    } deriving Show

data Equal = Exp :=: Exp deriving (Data,Typeable,Show,Eq)

data Goal = Goal Equal [(Equal, [Induction])] -- prove the ultimate goal, given a list of subgoals
            deriving Show

sym :: Equal -> Equal
sym (a :=: b) = b :=: a

resetState :: IO ()
resetState = withState $ const $ State [] [] []

invalid :: String -> a
invalid x = error $ "Proof step is invalid, " ++ x

promote :: State -> State
promote s@State{goals = Goal t []:xs} = promote $ s{proved = proved s ++ [(t,Proved)], goals = xs}
promote s@State{goals = Goal t ((a :=: b, _):gs):xs} | a == b = promote $ s{goals = Goal t gs : xs}
promote s = s

instance Pretty Equal where
    pretty (a :=: b) = pretty a ++ " = " ++ pretty b

instance Pretty State where
    pretty State{..} = unlines $
        [unwords $ "data" : x : "=" : intercalate ["|"] [fromCon y : replicate n "_" | (y,n) <- ys] | (x,ys) <- types] ++
        ["\n" ++ pretty x ++ (if b == Defined then " -- defined" else "") | (x,b) <- proved] ++
        ["\n-- GOAL\n" ++ pretty a ++ concat
            ["\n-- SUBGOAL " ++ show induct ++ "\n" ++
             pretty a | (a, induct) <- xs]
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
    withState $ \s -> s{goals = Goal (a :=: b) [(a :=: b, [])] : goals s}
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
    withState $ \s -> s{proved = proved s ++ [(prf, Defined)]}
    return prf

-- | Define a new data type, defines the case splitting rule.
defineData :: [(String,Int)] -> IO Equal
defineData ctrs = do
    withState $ \s -> s{proved = proved s ++ [(prf, Defined)]}
    return prf
    where
        v1:vs = fresh []
        prf = Lam v1 (Var v1) :=: Lam v1 (Case (Var v1) alts)
        alts = [(PCon (C a) vs', Con (C a) `apps` map Var vs') | (a,b) <- ctrs, let vs' = take b vs]


-- using the proof (which must be True, or inductively True) apply to produce this subgoal
applyProof :: Equal -> Equal -> IO ()
applyProof given@(from :=: to) new = withState $ \s ->
    if not $ valid s given then error $ "applyProof called with an invalid proof, " ++ pretty given else
        case goals s of
            Goal r1 ((old, reduced):r2):r3
                | new `elem` [ctx to | (val,ctx) <- contextsBi old, val == from]
                    -> s{goals = Goal r1 ((new, reduced):r2) : r3}
                | otherwise -> error $ "failed to match proof\n" ++ pretty given ++ "\n" ++ pretty old ++ "\n" ++ pretty new
    where
        valid s prf | prf `elem` map fst (proved s) || sym prf `elem` map fst (proved s) = True
                    | Goal t ((_,ind):_):_ <- goals s, prf `elem` [t, sym t] =
                        Coinduction `elem` ind
                    | otherwise = False

-- can only apply the induction in the case that

-- rewrite expressions, must be equivalent under eval
rewriteExp :: Equal -> IO ()
rewriteExp (a :=: b) = withSubgoal $ \(o@(x :=: y), reduced) ->
    if eval x /= eval a then invalid $ "rewriteExp\n" ++ pretty x ++ "\nNot equal to:\n" ++ pretty a
    else if eval y /= eval b then invalid $ "rewriteExp\n" ++ pretty y ++ "\nNot equal to:\n" ++ pretty b
    else [(a :=: b,reduced)]


splitCase :: IO ()
splitCase = withSubgoal $ \(o@(a :=: b), reduced) ->
    if pattern a /= pattern b then invalid $ "splitCase on different patterns, " ++ pretty o
    else let (vs,v,_) = pattern a
         in map (, [Coinduction | v `elem` map Var vs] ++ reduced) $ zipWith (:=:) (split a) (split b)
    where
        -- distinguishes the salient features
        pattern (fromLams . relabel -> (vs, Case on alts)) = (vs, on, map (patCon . fst) alts)
        pattern x = invalid $ "splitCase not on a case, " ++ pretty x

        split (fromLams -> (vs, Case on alts)) = [lams (vs ++ patVars p) x | (p,x) <- alts]


splitCon :: IO ()
splitCon = withSubgoal $ \(o@(a :=: b), _) ->
    if pattern a /= pattern b then invalid $ "splitCon on different patterns, " ++ pretty o
    else map (,[Coinduction]) $ zipWith (:=:) (split a) (split b)
    where
        pattern (fromLams -> (vs, fromApps -> (Con ctr, args))) = (length vs, ctr, length args)
        pattern x = invalid $ "splitCon not a con, " ++ pretty x

        split (fromLams -> (vs, fromApps -> (Con ctr, args))) = map (lams vs) args


splitOther :: IO ()
splitOther = withSubgoal $ \(o@(a :=: b), induct) ->
    if pattern a /= pattern b then invalid $ "splitVar on different patterns, " ++ pretty o
    else map (,induct) $ zipWith (:=:) (split a) (split b)
    where
        pattern (fromLams . relabel -> (vs, fromApps -> (Var v, args))) | v `elem` vs = (vs, v, length args)
        pattern x = invalid $ "splitVar not a free var, " ++ pretty x

        split (fromLams -> (vs, fromApps -> (Var v, args))) | v `elem` vs = map (lams vs) args


removeLam :: IO ()
removeLam = withSubgoal $ \(old@((fromLams -> (as, a)) :=: (fromLams -> (bs, b))), reduced) ->
    let rem = f as a `intersect` f bs b
        new = g rem as a :=: g rem bs b
    in if new == old then invalid "removeLam, none are redundant" else [(new, reduced)]
    where
        f as a = [i | let fr = free a, (i,x) <- zip [0..] as, x `notElem` fr]
        g rem as a = h [x | (i,x) <- zip [0..] as, i `notElem` rem] a
        h (unsnoc -> Just (vs,v)) (App x v2) | vs /= [], Var v == v2, v `notElem` free x = h vs x
        h a b = lams a b


{-# NOINLINE state #-}
state :: IORef State
state = unsafePerformIO $ newIORef $ State [] [] []

getState :: IO State
getState = readIORef state

getGoals = goals <$> getState
getProofs = map fst . proved <$> getState

withState :: (State -> State) -> IO ()
withState f = do
    s <- readIORef state
    s <- return $ promote $ f s
    evaluate $ rnf $ show s
    writeIORef state s

-- Nothing indicates you proved it
withGoal :: (Goal -> Goal) -> IO ()
withGoal f = withState $ \s@State{goals=g:gs} -> s{goals = f g : gs}

withSubgoal :: ((Equal, [Induction]) -> [(Equal, [Induction])]) -> IO ()
withSubgoal f = withGoal $ \(Goal t (p:ps)) -> Goal t (f p ++ ps)


cheat :: IO ()
cheat = withSubgoal (const [])
