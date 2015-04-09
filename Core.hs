{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Core(module Core) where

import Exp
import System.IO.Unsafe
import Data.IORef
import Data.Generics.Uniplate.Data
import Data.List
import Data.Data
import Simplify
import Data.Tuple.Extra


data State = State
    {types :: [(String, [(Con,Int)])] -- these should induce proofs
    ,proof :: [Equal]
    ,goals :: [Goal]
    }

-- trusted Core operations:
-- * Reorder goals
-- * Apply transformations to an expression
--   * Based on proof, direct textually equivalent equality substitution
--   * Based on eval equivalence
-- * Split based on Case, Ctor (induces a reduction)
-- * Reorder or drop lambda parameters equally (positional quantifiers)
-- * Induction, direct textually equivalent equality substitution


instance Show State where
    show State{..} = unlines $
        [unwords $ "data" : x : "=" : intercalate ["|"] [fromCon y : replicate n "_" | (y,n) <- ys] | (x,ys) <- types] ++
        ["\n" ++ pretty a ++ " = " ++ pretty b | a :=: b <- proof] ++
        ["\n-- GOAL\n" ++ pretty a ++ " = " ++ pretty b ++ concat
            ["\n-- SUBGOAL" ++ (if reduced then " (reduced)" else "") ++ "\n" ++
             pretty a ++ " = " ++ pretty b | (a :=: b, reduced) <- xs]
            | Goal (a :=: b) xs <- goals]


data Equal = Exp :=: Exp deriving (Data,Typeable)

data Goal = Goal Equal [(Equal, Bool)] -- prove the ultimate goal, given a list of subgoals, where True ones have been reduced

{-# NOINLINE state #-}
state :: IORef State
state = unsafePerformIO $ newIORef $ State [] [] []

withState :: (State -> State) -> IO ()
withState = modifyIORef state

-- Nothing indicates you proved it
withGoal :: (Goal -> Goal) -> IO ()
withGoal f = withState $ \s@State{goals=g:gs} -> case f g of
    Goal t [] -> s{goals = gs, proof = proof s ++ [t]}
    g -> s{goals = g:gs}

withSubgoal :: ((Equal, Bool) -> [(Equal, Bool)]) -> IO ()
withSubgoal f = withGoal $ \(Goal t (p:ps)) -> Goal t (f p ++ ps)

define :: String -> Exp -> IO ()
define a b = withState $ \s -> s{proof = (Var (V a) :=: b) : proof s}

goal :: Exp -> Exp -> IO ()
goal a b = withState $ \s -> s{goals = Goal (a :=: b) [(a :=: b, False)] : goals s}

defineP :: String -> String -> IO ()
defineP a b = define a (parse b)

goalP :: String -> String -> IO ()
goalP a b = goal (parse a) (parse b)

ctors :: String -> [(String,Int)] -> IO ()
ctors a b = withState $ \s -> s{types = (a,map (first C) b) : types s}

dump :: IO ()
dump = do
    s <- readIORef state
    print s


ask :: Exp -> IO Equal
ask x = do
    s <- readIORef state
    return $ head $ [a :=: b | a :=: b <- proof s, a == x] ++ error ("No proof found, " ++ show x)

askP :: String -> IO Equal
askP = ask . parse

apply :: Equal -> IO ()
apply (a :=: b) = withSubgoal $ \(t,reduced) ->
    case [ctx b | (val,ctx) <- contextsBi t, relabel val == relabel a] of
        new:_ -> [(new,reduced)]
        _ -> error $ "Trying to apply:\n" ++ f (a :=: b) ++ "\nTo:\n" ++ f t
    where
        f (a :=: b) = pretty a ++ " = " ++ pretty b

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

applyRhs :: Equal -> IO ()
applyRhs (a :=: b) = withSubgoal $ \(t,reduced) ->
    case [ctx b | (val,ctx) <- contextsBi $ swp t, relabel val == relabel a] of
        new:_ -> [(swp new,reduced)]
        _ -> error $ "Trying to apply:\n" ++ f (a :=: b) ++ "\nTo:\n" ++ f t
    where
        f (a :=: b) = pretty a ++ " = " ++ pretty b
        swp (a :=: b) = (b :=: a)

unfoldRhs :: String -> IO ()
unfoldRhs x = do p <- ask $ Var $ V x; applyRhs p


split :: String -> String -> IO ()
split = error "split"

simples :: IO ()
simples = withSubgoal $ \((a :=: b), reduced) -> [((simplify a :=: simplify b), reduced)]

splitRhs :: String -> IO ()
splitRhs typ = do
    s <- readIORef state
    let alts | Just ctrs <- lookup typ $ types s = [(PCon a vs, Con a `apps` map Var vs) | (a,b) <- ctrs, let vs = take b $ fresh []]
    withSubgoal $ \(a :=: b, reduced) ->
        case [ctx $ Case (Var var) alts | let bad = free b, (Var var, ctx) <- contextsBi b, var `notElem` bad] of
            b:_ -> [(a :=: b, reduced)]

peelCase :: IO ()
peelCase = withSubgoal $ \((fromLams -> (as,Case a a2)) :=: (fromLams -> (bs,Case b b2)), reduced) ->
    if as /= bs || a /= b || map fst a2 /= map fst b2 then error "different" else
        [ (lams (as ++ f pa) ea :=: lams (bs ++ f pb) eb, reduced) | ((pa,ea),(pb,eb)) <- zip a2 b2]
    where
        f (PCon _ vs) = vs
        f _ = []

peelCtor :: IO ()
peelCtor = withSubgoal $ \((fromLams -> (as, fromApps -> (Con a,a2))) :=: (fromLams -> (bs, fromApps -> (Con b, b2))), reduced) ->
    if as /= bs || a /= b || length a2 /= length b2 then error "different" else
        [(lams as a :=: lams bs b, True) | (a,b) <- zip a2 b2]


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
