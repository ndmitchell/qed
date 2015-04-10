{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Proofy(module Proofy, module Core) where

import Core
import Exp
import HSE
import Language.Haskell.Exts hiding (parse,Exp,Var,sym,Con,Case)
import Data.Generics.Uniplate.Data
import Data.List.Extra
import Simplify
import System.IO.Unsafe
import Data.IORef
import Data.Maybe
import Data.Tuple.Extra

data State2 = State2
    {names :: [(String, Equal)]
    ,applyRhs :: Bool
    ,applyInd :: Int
    }

{-# NOINLINE state2 #-}
state2 :: IORef State2
state2 = unsafePerformIO $ newIORef $ State2 [] False 0

reset :: IO ()
reset = do
    resetState
    writeIORef state2 $ State2 [] False 0

define :: String -> IO Equal
define x = case deflate $ fromParseResult $ parseDecl x of
    DataDecl _ _ _ name _ ctrs [] -> do
        let f (fromName -> x) = fromMaybe x $ lookup x [("Nil_","[]"),("Cons_",":")]
        ctors (f name) [(f a,length b) | (QualConDecl _ _ _ (ConDecl a b)) <- ctrs]
        return undefined
    PatBind _ (PVar x) (UnGuardedRhs bod) (BDecls []) -> do
        eq <- defineFunction (fromName x) (fromExp bod)
        named (fromName x) eq
        return eq
    x -> error $ "Define not handled, " ++ show x

named :: String -> Equal -> IO Equal
named a b = do modifyIORef state2 $ \s -> s{names = (a,b) : names s}; return b

goal :: String -> String -> IO Equal
goal a b = addGoal (parse a) (parse b)

ctors :: String -> [(String,Int)] -> IO ()
ctors a b = withState $ \s -> s{types = (a,map (first C) b) : types s}

dump :: IO ()
dump = do
    s <- getState
    putStrLn $ pretty s


ask :: String -> IO Equal
ask x = do
    s <- readIORef state2
    return $ fromMaybe (error $ "Proof not found named " ++ x) $ lookup x $ names s

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
unfold x = apply =<< ask x

refold :: String -> IO ()
refold x = apply . sym =<< ask x

unfoldEx :: Int -> String -> IO ()
unfoldEx i x = do p <- ask x; applyEx i p

rhs :: IO () -> IO ()
rhs act = swaps >> act >> swaps
    where swaps = withState $ \s -> s{goals = map f $ goals s}
          f (Goal a b) = Goal (g a) (map (first g) b)
          g (a :=: b) = b :=: a


simples :: IO ()
simples = do
    Goal _ ((a :=: b, _):_):_ <- getGoals
    rewriteExp (simplify a :=: simplify b)

split :: String -> IO ()
split typ = do
    s <- getState
    let alts | Just ctrs <- lookup typ $ types s = [(PCon a vs, Con a `apps` map Var vs) | (a,b) <- ctrs, let vs = take b $ fresh []]
    withSubgoal $ \(a :=: b, reduced) ->
        case [ctx $ Case (Var var) alts | let bad = free a, (Var var, ctx) <- contextsBi a, var `notElem` bad] of
            a:_ -> [(a :=: b, reduced)]


induct :: IO ()
induct = do
    Goal t _:_ <- getGoals
    apply t

relam :: [Int] -> IO ()
relam order = withSubgoal $ \((fromLams -> (as,a)) :=: (fromLams -> (bs,b)), reduced) ->
    if sort order /= [1..length as] || length as /= length bs then error "no relam" else
        [(lams (f as) a :=: lams (f bs) b, reduced)]
    where f xs = map (xs !!) $ map pred order
