{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Proofy(
    run, dump, reset,
    define, goal, auto, proof, unauto,
    unfold, refold, simples, induct, splitCase, splitCon, splitOther, removeLam, equal, unlet, push,
    apply, rhs, at, ats, unify,
    cheat, sym
    ) where


import Core
import Exp
import HSE
import Language.Haskell.Exts hiding (parse,Exp,Var,sym,Con,Case,App,Let)
import Data.Generics.Uniplate.Data
import Control.Exception.Extra
import Control.Applicative
import Data.List.Extra
import Simplify
import System.IO.Unsafe
import Data.IORef
import Data.Maybe
import Control.Monad.Extra
import Data.Either.Extra


data State2 = State2
    {names :: [(String, Equal)]
    ,applyRhs :: Bool
    ,applyAt :: Maybe Int
    ,applyUnify :: Bool
    ,autos :: [IO ()]
    }

run :: IO a -> IO ()
run act = flip onException dump $ do
    reset
    act
    dump
    g <- getGoals
    when (null g) $ putStrLn "QED"

auto :: IO () -> IO ()
auto x = modifyIORef state2 $ \s -> s{autos = autos s ++ [x]}

unauto :: IO () -> IO ()
unauto act = do
    aut <- fmap autos $ readIORef state2
    modifyIORef state2 $ \s -> s{autos = []}
    act
    modifyIORef state2 $ \s -> s{autos = aut}

runAutos :: IO ()
runAutos = do
    State2{..} <- readIORef state2
    whileM $ any isRight <$> mapM try_ autos


{-# NOINLINE state2 #-}
state2 :: IORef State2
state2 = unsafePerformIO $ newIORef $ State2 [] False (Just 0) False []

reset :: IO ()
reset = do
    resetState
    writeIORef state2 $ State2 [] False (Just 0) False []

define :: String -> IO Equal
define x = case deflate $ fromParseResult $ parseDecl x of
    DataDecl _ _ _ name _ ctrs [] -> do
        let f (fromName -> x) = fromMaybe x $ lookup x [("Nil_","[]"),("Cons_",":")]
        eq <- defineData [(f a,length b) | (QualConDecl _ _ _ (ConDecl a b)) <- ctrs]
        named (f name) eq
        return eq
    PatBind _ (PVar x) (UnGuardedRhs bod) (BDecls []) -> do
        eq <- defineFunction (fromName x) (fromExp bod)
        named (fromName x) eq
        return eq
    x -> error $ "Define not handled, " ++ show x

named :: String -> Equal -> IO Equal
named a b = do modifyIORef state2 $ \s -> s{names = (a,b) : names s}; return b

goal :: String -> String -> IO Equal
goal a b = addGoal (parse a) (parse b)

proof :: String -> String -> IO () -> IO Equal
proof (parse -> a) (parse -> b) c = do
    done <- getProofs
    let prf = a :=: b
    when (prf `notElem` done) $ do
        pre <- getGoals
        eq <- addGoal a b
        c
        post <- getGoals
        when (length pre /= length post) $ error "proof did not prove the goal"
    return prf

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
    case [ do let args = [fromMaybe (Con $ C "_") $ lookup v sub | v <- as]
              rewriteExp $ swp $ ctx $ apps (lams as a) args
              applyProof prf $ swp $ ctx $ apps b args
         | (val,ctx) <- contextsBi $ swp t, Just sub <- [unifier as a val], applyUnify || all (isVar . snd) sub] of
        new | length new > fromJust applyAt -> new !! fromJust applyAt
        _ -> error $ "Trying to apply:\n" ++ pretty prf ++ "\nTo:\n" ++ pretty t
    runAutos


isVar Var{} = True; isVar _ = False

-- if you were to subtitute the binding in the first expression, you would come up with something equivalent to the second
unifier :: [Var] -> Exp -> Exp -> Maybe [(Var, Exp)]
unifier fv = f []
    where
        f sub (Var x) y | x `elem` fv, x `notElem` map fst sub = Just [(x, y)]
        f sub (Var x) (Var y) | (x,y) `elem` sub || (x `notElem` fv && x `notElem` map fst sub && y `notElem` map snd sub && x == y) = Just []
        f sub (Con c1) (Con c2) = Just []
        f sub (App x1 y1) (App x2 y2) = f sub x1 x2 & f sub y1 y2
        f sub (Lam v1 x1) (Lam v2 x2) = f ((v1,v2):sub) x1 x2
        f sub (Case o1 a1) (Case o2 a2) | length a1 == length a2 = foldr (&) (f sub o1 o2) $ zipWith g a1 a2
            where g (PCon c1 vs1, b1) (PCon c2 vs2, b2) | c1 == c2 && length vs1 == length vs2 = f (zip vs1 vs2 ++ sub) b1 b2
                  g (PWild, b1) (PWild, b2) = f sub b1 b2
                  g _ _ = Nothing
        f _ _ _ = Nothing

        Just a & Just b | let ab = nubOrd $ a ++ b, length (nubOrd $ map fst ab) == length ab = Just ab
        _ & _ = Nothing


unfold :: String -> IO ()
unfold x = apply =<< ask x

refold :: String -> IO ()
refold x = apply . sym =<< ask x


simples :: IO ()
simples = do
    whenM (null <$> getGoals) $ error "Nothing to simplify"
    Goal _ ((a :=: b, _):_):_ <- getGoals
    let a2 = simplify a
    let b2 = simplify b
    when (a2 == a && b2 == b) $ error "Simplification didn't acheive anything"
    rewriteExp (simplify a :=: simplify b)

induct :: IO ()
induct = do
    Goal t _:_ <- getGoals
    apply t

equal :: IO ()
equal = do
    Goal t ((a :=: b, _):_) : _ <- getGoals
    rewriteExp $ b :=: b

unlet :: IO ()
unlet = do
    Goal _ ((p, _):_) : _ <- getGoals
    rewriteExp $ head $ [ctx $ subst [(a,b)] c | (Let a b c, ctx) <- contextsBi p]
    runAutos

push :: IO ()
push = do
    Goal _ ((p, _):_) : _ <- getGoals
    rewriteExp $ head $ [ctx $ subst [(a,b)] c | (Let a b c, ctx) <- contextsBi p]
    runAutos
