{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Proofy(module Proofy, module Core) where

import Core
import Exp
import HSE
import Language.Haskell.Exts hiding (parse,Exp,Var,sym,Con,Case,App)
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
    ,applyAt :: Maybe Int
    ,applyUnify :: Bool
    }

{-# NOINLINE state2 #-}
state2 :: IORef State2
state2 = unsafePerformIO $ newIORef $ State2 [] False (Just 0) False

reset :: IO ()
reset = do
    resetState
    writeIORef state2 $ State2 [] False (Just 0) False

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
    (do s <- readIORef state2; writeIORef state2 s{applyAt=Just i}; return $ applyAt s)
    (\v -> modifyIORef state2 $ \s -> s{applyAt=v})
    . const

ats :: IO a -> IO a
ats = bracket
    (do s <- readIORef state2; writeIORef state2 s{applyAt=Nothing}; return $ applyAt s)
    (\v -> modifyIORef state2 $ \s -> s{applyAt=v})
    . const

unify :: IO a -> IO a
unify = bracket
    (do s <- readIORef state2; writeIORef state2 s{applyUnify=True}; return $ applyUnify s)
    (\v -> modifyIORef state2 $ \s -> s{applyUnify=v})
    . const

apply :: Equal -> IO ()
apply prf@((fromLams -> (as,a)) :=: b) = do
    State2{..} <- readIORef state2
    let swp = if applyRhs then sym else id
    Goal _ ((t,_):_):_ <- getGoals
    case [ do rewriteExp $ swp $ ctx $ apps (lams as a) $ map snd sub
              applyProof prf $ swp $ ctx $ apps b $ map snd sub
         | (val,ctx) <- contextsBi $ swp t, Just sub <- [unifier as a val], applyUnify || all (isVar . snd) sub] of
        new | length new > fromJust applyAt -> new !! fromJust applyAt
        _ -> error $ "Trying to apply:\n" ++ pretty (a :=: b) ++ "\nTo:\n" ++ pretty t

isVar Var{} = True; isVar _ = False

-- if you were to subtitute the binding in the first expression, you would come up with something equivalent to the second
unifier :: [Var] -> Exp -> Exp -> Maybe [(Var, Exp)]
unifier fv a b = f fv (relabel a) (relabel b)
    where
        f fv (Var x) y | x `elem` fv = Just [(x, y)]
        f fv (Con c1) (Con c2) = Just []
        f fv (App x1 y1) (App x2 y2) = f fv x1 x2 & f fv y1 y2
        f fv (relabel -> Lam v1 x1) (relabel -> Lam v2 x2) | v1 == v2 = f (delete v1 fv) x1 x2
        f fv (Var x) (Var y) | x `notElem` fv, x == y = Just []
        f _ _ _ = Nothing

        Just a & Just b | let ab = nubOrd $ a ++ b, length (nubOrd $ map fst ab) == length ab = Just ab
        _ & _ = Nothing


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
