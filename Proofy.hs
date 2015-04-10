{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Proofy(module Proofy, module Core) where

import Core
import Exp
import HSE
import Language.Haskell.Exts hiding (parse,Exp,Var,sym,Con,Case)
import Data.Generics.Uniplate.Data
import Control.Exception
import Data.List.Extra
import Simplify
import System.IO.Unsafe
import Data.IORef
import Data.Maybe
import Data.Tuple.Extra

data State2 = State2
    {names :: [(String, Equal)]
    ,applyRhs :: Bool
    ,applyAt :: Int
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
        let ctors a b = withState $ \s -> s{types = (a,map (first C) b) : types s}

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

dump :: IO ()
dump = do
    s <- getState
    putStrLn $ pretty s

ask :: String -> IO Equal
ask x = do
    s <- readIORef state2
    return $ fromMaybe (error $ "Proof not found named " ++ x) $ lookup x $ names s

rhs :: IO a -> IO a
rhs = bracket
    (do s <- readIORef state2; writeIORef state2 s{applyRhs=True}; return $ applyRhs s)
    (\v -> modifyIORef state2 $ \s -> s{applyRhs=v})
    . const

at :: Int -> IO a -> IO a
at i = bracket
    (do s <- readIORef state2; writeIORef state2 s{applyAt=i}; return $ applyAt s)
    (\v -> modifyIORef state2 $ \s -> s{applyAt=v})
    . const

apply :: Equal -> IO ()
apply (a :=: b) = do
    State2{..} <- readIORef state2
    let swp = if applyRhs then sym else id
    withSubgoal $ \(t,reduced) ->
        case [swp $ ctx b | (val,ctx) <- contextsBi $ swp t, relabel val == relabel a] of
            new | length new > applyAt -> [(new !! applyAt,reduced)]
            _ -> error $ "Trying to apply:\n" ++ pretty (a :=: b) ++ "\nTo:\n" ++ pretty t


unfold :: String -> IO ()
unfold x = apply =<< ask x

refold :: String -> IO ()
refold x = apply . sym =<< ask x


simples :: IO ()
simples = do
    Goal _ ((a :=: b, _):_):_ <- getGoals
    rewriteExp (simplify a :=: simplify b)

split :: String -> IO ()
split typ = do
    State2{..} <- readIORef state2
    let swp = if applyRhs then sym else id
    s <- getState
    let alts | Just ctrs <- lookup typ $ types s = [(PCon a vs, Con a `apps` map Var vs) | (a,b) <- ctrs, let vs = take b $ fresh []]
    withSubgoal $ \((swp -> a :=: b), reduced) ->
        case [ctx $ Case (Var var) alts | let bad = free a, (Var var, ctx) <- contextsBi a, var `notElem` bad] of
            a:_ -> [(swp $ a :=: b, reduced)]


induct :: IO ()
induct = do
    Goal t _:_ <- getGoals
    apply t

relam :: [Int] -> IO ()
relam order = withSubgoal $ \((fromLams -> (as,a)) :=: (fromLams -> (bs,b)), reduced) ->
    if sort order /= [1..length as] || length as /= length bs then error "no relam" else
        [(lams (f as) a :=: lams (f bs) b, reduced)]
    where f xs = map (xs !!) $ map pred order
