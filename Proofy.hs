{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Proofy(
    run,
    define,
    proof,
    unfold,
    unlet,
    expand,
    recurse,
    cheat,
    rhs,
    twice
    ) where


import Exp
import HSE
import Util
import Language.Haskell.Exts hiding (parse,Exp,Var,sym,Con,Case,App,Let,Pretty(..))
import Data.Generics.Uniplate.Data
import Control.Exception.Extra
import Control.Applicative
import Data.List.Extra
import Control.DeepSeq
import Simplify
import System.IO.Unsafe
import Data.IORef
import Data.Maybe
import Control.Monad.Extra
import Data.Either.Extra
import Data.Data


data Equal = Exp :=: Exp deriving (Show,Data,Eq)

sym :: Equal -> Equal
sym (a :=: b) = (b :=: a)

twice x = x >> x

data State = State
    {defined :: [(Var, Exp)]
    ,proved :: [Equal]
    ,types :: [(String, [(Con,Int)])]
    ,goal :: [Goal] -- A list of And alternatives
    ,focusRhs :: Bool
    ,focusInd :: Int
    } deriving Show

instance NFData State where
    rnf x = rnf $ show x

instance Pretty Equal where
    pretty (a :=: b) = pretty a ++ " :=: " ++ pretty b

instance Pretty State where
    pretty State{..} = unlines $
        [unwords $ "data" : x : "=" : intercalate ["|"] [fromCon y : replicate n "_" | (y,n) <- ys] | (x,ys) <- types] ++
        ["\n" ++ fromVar x ++ " = " ++ pretty b | (x,b) <- defined] ++
        ["\n" ++ pretty x | x <- proved] ++
        ["\n-- GOAL" ++ concat ["\n-- WHERE " ++ pretty p | p <- pre] ++ "\n" ++ pretty x | Goal pre x <- goal]

state0 = State [] [] [] [] False 0

data Goal = Goal [Equal] Equal deriving (Show,Eq)

Just a =^= Just b = a == b
_ =^= _ = False

state :: IORef State
state = unsafePerformIO $ newIORef $ state0

getState :: IO State
getState = readIORef state

modifyState :: (State -> State) -> IO ()
modifyState f = do
    s <- readIORef state
    let s2 = f s
    evaluate $ rnf s2
    writeIORef state s2

rhs :: IO a -> IO a
rhs f = bracket getState (\v -> modifyState $ \s -> s{focusRhs=focusRhs v}) (\_ -> do modifyState $ \s -> s{focusRhs=True}; f)

run :: IO a -> IO ()
run act = flip onException dump $ do
    writeIORef state state0
    act
    dump
    g <- goal <$> getState
    when (null g) $ putStrLn "QED"

dump :: IO ()
dump = do
    x <- getState
    putStrLn $ pretty x


define :: String -> IO ()
define x = case deflate $ fromParseResult $ parseDecl x of
    DataDecl _ _ _ name _ ctrs [] -> do
        let f (fromName -> x) = fromMaybe x $ lookup x [("Nil_","[]"),("Cons_",":")]
        modifyState $ \s -> s{types = (f name, [(C $ f a,length b) | (QualConDecl _ _ _ (ConDecl a b)) <- ctrs]) : types s}
    PatBind _ (PVar x) (UnGuardedRhs bod) (BDecls []) -> do
        modifyState $ \s -> s{defined = (V $ fromName x, fromExp bod) : defined s}
    x -> error $ "Define not handled, " ++ show x

proof :: String -> String -> IO () -> IO ()
proof (parse -> a) (parse -> b) c = do
    g <- goal <$> getState
    unless (null g) $ error "Can't call proof recursively"
    modifyState $ \s -> s{goal = [Goal [] (a :=: b)]}
    c
    g <- goal <$> getState
    unless (null g) $ error "proof did not prove the goal"
    modifyState $ \s -> s{proved = proved s ++ [a :=: b]}

expand :: IO ()
expand = auto $ modifyState $ \s ->
    let Goal pre x:gs = goal s
        swp = if focusRhs s then sym else id
        eta (o@(fromLams -> (vs,x)) :=: b) | v:_ <- fresh $ vars o = lams (vs ++ [v]) (App x $ Var v) :=: b
    in s{goal = Goal pre (swp $ eta $ swp x):gs}

unfold :: String -> IO ()
unfold x = auto $ modifyState $ \s -> case () of
    _ | Just e <- lookup (V x) $ defined s ->
        let Goal pre g1:gs = goal s
            swp = if focusRhs s then sym else id
            g2 = head $ [swp $ gen e | (Var (V v), gen) <- contextsBi $ swp g1, v == x] ++ error "nothing matches unfold"
        in s{goal = Goal pre g2:gs}
    _ | Just e <- lookup x $ types s ->
        let Goal pre g1:gs = goal s
            swp = if focusRhs s then sym else id
            alts = [(PCon c vs, apps (Con c) (map Var vs)) | (c, n) <- e, let vs = take n $ fresh []]
            g2 = head $ [swp $ gen $ Case (Var $ V v) alts | (Var (V v), gen) <- contextsBi $ swp g1] ++ error "nothing matches unfold"
        in s{goal = Goal pre g2:gs}
    _ -> error $ "Unknown unfolding for " ++ x

unlet :: IO ()
unlet = auto $ modifyState $ \s ->
    let Goal pre g1:gs = goal s
        swp = if focusRhs s then sym else id
        g2 = head $ [swp $ gen $ subst [(a,b)] x | (Let a b x, gen) <- contextsBi $ swp g1] ++ error "nothing matches unlet"
    in s{goal = Goal pre g2:gs}

auto :: IO a -> IO a
auto act = do
    res <- act
    let f act = do x1 <- getState; act; x2 <- getState; return $ goal x1 /= goal x2
    whileM $ anyM f [autoLaw,autoSimplify,autoPeelCase,autoPeelCon,autoRemoveLam,autoPeelVar]
    return res

cheat :: IO ()
cheat = modifyState $ \s -> s{goal = []}

autoSimplify :: IO ()
autoSimplify = modifyState $ \s ->
    s{goal = [Goal pre (simplify a :=: simplify b) | Goal pre (a :=: b) <- goal s]}

autoLaw :: IO ()
autoLaw = modifyState $ \s -> s{goal = filter (not . taut (proved s)) $ goal s}
    where
        taut extra (Goal pre (a :=: b)) =
            a == b || any (`appeal` (norm (a :=: b))) (map norm $ pre ++ extra ++ map sym (pre ++ extra))

autoPeelCase :: IO ()
autoPeelCase = modifyState $ \s -> s{goal = concat [map (Goal pre) $ f x | Goal pre x <- goal s]}
    where
        f (a :=: b) | pattern a =^= pattern b = zipWith (:=:) (split a) (split b)
        f x = [x]

        -- distinguishes the salient features
        pattern (fromLams . relabel -> (vs, Case on alts)) = Just (vs, on, map (patCon . fst) alts)
        pattern x = Nothing

        split (fromLams -> (vs, Case on alts)) = [lams (vs ++ patVars p) x | (p,x) <- alts]


autoPeelCon :: IO ()
autoPeelCon = modifyState $ \s -> s{goal = concat [map (Goal pre) $ f x | Goal pre x <- goal s]}
    where
        f (a :=: b) | pattern a =^= pattern b = zipWith (:=:) (split a) (split b)
        f x = [x]

        pattern (fromLams -> (vs, fromApps -> (Con ctr, args))) = Just (length vs, ctr, length args)
        pattern x = Nothing

        split (fromLams -> (vs, fromApps -> (Con ctr, args))) = map (lams vs) args

autoPeelVar :: IO ()
autoPeelVar = modifyState $ \s -> s{goal = concat [map (Goal pre) $ f x | Goal pre x <- goal s]}
    where
        f (a :=: b) | pattern a =^= pattern b = zipWith (:=:) (split a) (split b)
        f x = [x]

        pattern (fromLams . relabel -> (vs, fromApps -> (Var v, args))) | v `elem` vs = Just (vs, v, length args)
        pattern x = Nothing

        split (fromLams -> (vs, fromApps -> (Var v, args))) | v `elem` vs = map (lams vs) args


autoRemoveLam :: IO ()
autoRemoveLam = modifyState $ \s -> s{goal = [Goal pre $ f x | Goal pre x <- goal s]}
    where
        f (a :=: b) | unused <- pattern a `intersect` pattern b = split unused a :=: split unused b

        pattern (fromLams -> (vs, x)) = [i | (i,v) <- zip [0..] vs, v `notElem` free x]
        split unused (fromLams -> (vs, x)) = lams [v | (i,v) <- zip [0..] vs, i `notElem` unused] x

recurse :: IO ()
recurse = auto $ modifyState $ \s ->
    let Goal pre (a:=:b):gs = goal s
    in case (step s a, step s b) of
        (Nothing, Nothing) -> error $ "Cannot step\n" ++ pretty a ++ "\n" ++ pretty b
        (aa, bb) -> s{goal = Goal ((simplify a:=:simplify b) : pre) (fromMaybe a aa :=: fromMaybe b bb):gs}



step :: State -> Exp -> Maybe Exp
step State{..} = f
    where
        f (Lam v x) = Lam v <$> f x
        f (App a b) = (`App` b) <$> f a
        f (Var v) = lookup v defined
        f (Case x xs) = (`Case` xs) <$> f x
        f x = error $ "step: Don't know, " ++ pretty x


appeal :: Equal -> Equal -> Bool
appeal (a :=: b) (aa :=: bb) = a == aa && b == bb {- f a aa =^= f b bb
    where
        f (g -> (aa,a)) (g -> (bb,b)) = if a == b then Just (aa,bb) else Nothing

        g (uneta -> (aa1,relbl -> (aa2,a))) = ((aa1,aa2),a)

        uneta (fromLams -> (vs, App x (Var (V v))))
            | v `notElem` free x, Just i <- elemIndex v vs  = first (i:) $ uneta $ lams vs x
        uneta x = ([], x)

        relbl (lams -> (xs, x)) = (mapMaybe (`findIndex` xs) $ nub $ free x, x)
-}


norm :: Equal -> Equal
norm (a :=: b) = (f va xa :=: f vb xb)
    where
        (va, xa) = fromLams $ simplify a
        (vb, xb) = fromLams $ simplify b
        n = length $ takeWhile (uncurry (==)) $ zip va vb
        com = nub (free xa ++ free xb) `intersect` take n va

        f vs x = simplify $ lams (com ++ (vs \\ com)) x
