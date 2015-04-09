{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Core(module Core) where

import Exp
import System.IO.Unsafe
import Data.IORef
import Data.Generics.Uniplate.Data
import Data.List.Extra
import Data.Data
import Simplify
import Data.Tuple.Extra


data State = State
    {types :: [(String, [(Con,Int)])] -- these should go away
    ,defined :: [String] -- stop things being redefined
    ,proof :: [Equal]
    ,goals :: [Goal] -- none are literally equal
    }

data Equal = Exp :=: Exp deriving (Data,Typeable,Show,Eq)

data Goal = Goal Equal [(Equal, Bool)] -- prove the ultimate goal, given a list of subgoals, where True ones have been reduced

sym :: Equal -> Equal
sym (a :=: b) = b :=: a

reset = withState $ const $ State [] [] [] []


promote :: State -> State
promote s@State{goals = Goal t []:xs} = promote $ s{proof = proof s ++ [t], goals = xs}
promote s@State{goals = Goal t ((a :=: b, _):gs):xs} | a == b = promote $ s{goals = Goal t gs : xs}
promote s = s

instance Show State where
    show State{..} = unlines $
        [unwords $ "data" : x : "=" : intercalate ["|"] [fromCon y : replicate n "_" | (y,n) <- ys] | (x,ys) <- types] ++
        ["\n" ++ pretty a ++ " = " ++ pretty b | a :=: b <- proof] ++
        ["\n-- GOAL\n" ++ pretty a ++ " = " ++ pretty b ++ concat
            ["\n-- SUBGOAL" ++ (if reduced then " (reduced)" else "") ++ "\n" ++
             pretty a ++ " = " ++ pretty b | (a :=: b, reduced) <- xs]
            | Goal (a :=: b) xs <- goals]


-- trusted Core operations:
-- * Reorder goals
-- * Apply transformations to an expression
--   * Based on proof, direct textually equivalent equality substitution
--   * Based on eval equivalence
-- * Split based on Case, Ctor (induces a reduction)
-- * Reorder or drop lambda parameters equally (positional quantifiers)
-- * Induction, direct textually equivalent equality substitution

addGoal :: Exp -> Exp -> IO ()
addGoal a b = withState $ \s -> s{goals = Goal (a :=: b) [(a :=: b, False)] : goals s}


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
defineFunction :: String -> Exp -> IO ()
defineFunction name body = withState $ \s ->
    if name `elem` defined s then error $ "Already defined function, " ++ name else
        s{defined = name : defined s, proof = proof s ++ [Var (V name) :=: body]}


-- | Define a new data type, defines the case splitting rule.
defineData :: [(String,Int)] -> IO ()
defineData ctrs = withState $ \s ->
    if not $ disjoint (map fst ctrs) (defined s) then error $ "Already defined data, " ++ show ctrs else
        s{defined = map fst ctrs ++ defined s, proof = proof s ++ [prf]}
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
        valid s prf | prf `elem` proof s = True
                    | sym prf `elem` proof s = True
                    | Goal t ((_,True):_):_ <- goals s, prf `elem` [t, sym t] = True
                    | otherwise = False


-- rewrite expressions, must be equivalent under eval
rewriteExp :: Equal -> IO ()
rewriteExp (a :=: b) = withSubgoal $ \(x :=: y, reduced) ->
    if eval x == eval a &&  eval y == eval b then [(a :=: b,reduced)] else error "rewriteExp, not equal"


splitCase :: IO ()
splitCase = withSubgoal $ \((fromLams -> (as,Case a a2)) :=: (fromLams -> (bs,Case b b2)), reduced) ->
    if as /= bs || a /= b || map fst a2 /= map fst b2 then error "different" else
        [ (lams (as ++ f pa) ea :=: lams (bs ++ f pb) eb, reduced) | ((pa,ea),(pb,eb)) <- zip a2 b2]
    where
        f (PCon _ vs) = vs
        f _ = []


splitCon :: IO ()
splitCon = withSubgoal $ \((fromLams -> (as, fromApps -> (Con a,a2))) :=: (fromLams -> (bs, fromApps -> (Con b, b2))), reduced) ->
    if as /= bs || a /= b || length a2 /= length b2 then error "different" else
        [(lams as a :=: lams bs b, True) | (a,b) <- zip a2 b2]


-- technically not necessary, just cleans up quantifiers
removeLam :: IO ()
removeLam = undefined




{-# NOINLINE state #-}
state :: IORef State
state = unsafePerformIO $ newIORef $ State [] [] [] []

withState :: (State -> State) -> IO ()
withState f = modifyIORef state (promote . f)

-- Nothing indicates you proved it
withGoal :: (Goal -> Goal) -> IO ()
withGoal f = withState $ \s@State{goals=g:gs} -> case f g of
    Goal t [] -> s{goals = gs, proof = proof s ++ [t]}
    g -> s{goals = g:gs}

withSubgoal :: ((Equal, Bool) -> [(Equal, Bool)]) -> IO ()
withSubgoal f = withGoal $ \(Goal t (p:ps)) -> Goal t (f p ++ ps)

define :: String -> Exp -> IO ()
define = defineFunction

ctors :: String -> [(String,Int)] -> IO ()
ctors a b = withState $ \s -> s{types = (a,map (first C) b) : types s}

goal = addGoal

dump :: IO ()
dump = do
    s <- readIORef state
    print s


ask :: Exp -> IO Equal
ask x = do
    s <- readIORef state
    return $ head $ [a :=: b | a :=: b <- proof s, a == x] ++ error ("No proof found, " ++ show x)

apply :: Equal -> IO ()
apply = applyEx 0

applyEx :: Int -> Equal -> IO ()
applyEx i (a :=: b) = withSubgoal $ \(t,reduced) ->
    case [ctx b | (val,ctx) <- contextsBi t, relabel val == relabel a] of
        new | length new > i -> [(new !! i,reduced)]
        _ -> error $ "Trying to apply:\n" ++ f (a :=: b) ++ "\nTo:\n" ++ f t
    where
        f (a :=: b) = pretty a ++ " = " ++ pretty b

unfold :: String -> IO ()
unfold x = do p <- ask $ Var $ V x; apply p

unfoldEx :: Int -> String -> IO ()
unfoldEx i x = do p <- ask $ Var $ V x; applyEx i p

rhs :: IO () -> IO ()
rhs act = swaps >> act >> swaps
    where swaps = withState $ \s -> s{goals = map f $ goals s}
          f (Goal a b) = Goal (g a) (map (first g) b)
          g (a :=: b) = b :=: a


simples :: IO ()
simples = withSubgoal $ \((a :=: b), reduced) -> [((simplify a :=: simplify b), reduced)]

split :: String -> IO ()
split typ = do
    s <- readIORef state
    let alts | Just ctrs <- lookup typ $ types s = [(PCon a vs, Con a `apps` map Var vs) | (a,b) <- ctrs, let vs = take b $ fresh []]
    withSubgoal $ \(a :=: b, reduced) ->
        case [ctx $ Case (Var var) alts | let bad = free a, (Var var, ctx) <- contextsBi a, var `notElem` bad] of
            a:_ -> [(a :=: b, reduced)]

peelCase :: IO ()
peelCase = splitCase

peelCtor :: IO ()
peelCtor = splitCon


eq :: IO ()
eq = withSubgoal $ \(a :=: b, _) -> if eval a /= eval b then error "not equivalent" else []

induct :: IO ()
induct = do
    State{goals=Goal t _:_} <- readIORef state
    apply t

relam :: [Int] -> IO ()
relam order = withSubgoal $ \((fromLams -> (as,a)) :=: (fromLams -> (bs,b)), reduced) ->
    if sort order /= [1..length as] || length as /= length bs then error "no relam" else
        [(lams (f as) a :=: lams (f bs) b, reduced)]
    where f xs = map (xs !!) $ map pred order
