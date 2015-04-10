{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Proofy(module Proofy, module Core) where

import Core
import Exp
import Data.Generics.Uniplate.Data
import Data.List.Extra
import Simplify
import Data.Tuple.Extra

reset :: IO ()
reset = resetState

define :: String -> String -> IO Equal
define a b = defineFunction a (parse b)

goal :: String -> String -> IO Equal
goal a b = addGoal (parse a) (parse b)

askP :: String -> IO Equal
askP = ask . parse

ctors :: String -> [(String,Int)] -> IO ()
ctors a b = withState $ \s -> s{types = (a,map (first C) b) : types s}

dump :: IO ()
dump = do
    s <- getState
    putStrLn $ pretty s


ask :: Exp -> IO Equal
ask x = do
    s <- getState
    return $ head $ [a :=: b | (a :=: b,_) <- proof s, a == x] ++ error ("No proof found, " ++ show x)

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

refold :: String -> IO ()
refold x = do p <- ask $ Var $ V x; apply $ sym p

unfoldEx :: Int -> String -> IO ()
unfoldEx i x = do p <- ask $ Var $ V x; applyEx i p

rhs :: IO () -> IO ()
rhs act = swaps >> act >> swaps
    where swaps = withState $ \s -> s{goals = map f $ goals s}
          f (Goal a b) = Goal (g a) (map (first g) b)
          g (a :=: b) = b :=: a


simples :: IO ()
simples = do
    State{goals=Goal _ ((a :=: b, _):_):_} <- getState
    rewriteExp (simplify a :=: simplify b)

split :: String -> IO ()
split typ = do
    s <- getState
    let alts | Just ctrs <- lookup typ $ types s = [(PCon a vs, Con a `apps` map Var vs) | (a,b) <- ctrs, let vs = take b $ fresh []]
    withSubgoal $ \(a :=: b, reduced) ->
        case [ctx $ Case (Var var) alts | let bad = free a, (Var var, ctx) <- contextsBi a, var `notElem` bad] of
            a:_ -> [(a :=: b, reduced)]


eq :: IO ()
eq = withSubgoal $ \(a :=: b, _) -> if eval a /= eval b then error "not equivalent" else []

induct :: IO ()
induct = do
    State{goals=Goal t _:_} <- getState
    apply t

relam :: [Int] -> IO ()
relam order = withSubgoal $ \((fromLams -> (as,a)) :=: (fromLams -> (bs,b)), reduced) ->
    if sort order /= [1..length as] || length as /= length bs then error "no relam" else
        [(lams (f as) a :=: lams (f bs) b, reduced)]
    where f xs = map (xs !!) $ map pred order
