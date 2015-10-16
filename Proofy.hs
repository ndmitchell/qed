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
    divide,
    unsafeReplace,
    rhs, ind
    ) where

import Exp
import Prop
import HSE
import Util
import Language.Haskell.Exts hiding (parse,Exp,Var,sym,Con,Case,App,Let,Pretty(..))
import Data.Generics.Uniplate.Data
import Control.Exception.Extra
import Data.List.Extra
import Control.DeepSeq
import System.IO.Unsafe
import Data.IORef
import Data.Maybe
import Control.Monad.Extra


data State = State
    {defined :: [(Var, Exp)]
    ,types :: [(String, [(Con,Int)])]
    ,proved :: [Prop]
    ,goal :: [Goal] -- A list of And alternatives
    ,focusRhs :: Bool
    ,focusInd :: Int
    } deriving Show

instance NFData State where
    rnf x = rnf $ show x

instance Pretty State where
    pretty State{..} = unlines $
        [unwords $ "data" : x : "=" : intercalate ["|"] [fromCon y : replicate n "_" | (y,n) <- ys] | (x,ys) <- types] ++
        ["\n" ++ fromVar x ++ " = " ++ pretty b | (x,b) <- defined] ++
        ["\n" ++ pretty x | x <- proved] ++
        ["\n-- GOAL " ++ show i ++ concat ["\n-- WHERE " ++ pretty p | p <- pre] ++ "\n" ++ pretty x | (i,Goal pre x) <- zip [1..] goal]

state0 = State [] [] [] [] False 0

data Goal = Goal [Prop] Prop deriving (Show,Eq)

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
rhs f = bracket getState
    (\v -> modifyState $ \s -> s{focusRhs=focusRhs v})
    (\_ -> do modifyState $ \s -> s{focusRhs=True}; f)

ind :: Int -> IO a -> IO a
ind i f = bracket getState
    (\v -> modifyState $ \s -> s{focusInd=focusInd v})
    (\_ -> do modifyState $ \s -> s{focusInd=i}; f)

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

cheat :: IO ()
cheat = modifyState $ \s -> s{goal = []}

define :: String -> IO ()
define x = case deflate $ fromParseResult $ parseDecl x of
    DataDecl _ _ _ name _ ctrs _ -> do
        let f (fromName -> x) = fromMaybe x $ lookup x [("Nil_","[]"),("Cons_",":")]
        modifyState $ \s -> s{types = types s ++ [(f name, [(C $ f a,length b) | (QualConDecl _ _ _ (ConDecl a b)) <- ctrs])]}
    PatBind _ (PVar x) (UnGuardedRhs bod) (BDecls []) -> do
        let res = fromExp bod
        evaluate $ show res
        modifyState $ \s -> s{defined = defined s ++ [(V $ fromName x, res)]}
    x -> error $ "Define not handled, " ++ show x

proof :: String -> String -> IO () -> IO (IO ())
proof (parse -> a) (parse -> b) c = do
    g <- goal <$> getState
    unless (null g) $ error "Can't call proof recursively"
    let p = simplifyProp $ Prop [] a b
    modifyState $ \s -> s{goal = auto s $ Goal [] p}
    c
    g <- goal <$> getState
    unless (null g) $ error "proof did not prove the goal"
    modifyState $ \s -> s{proved = proved s ++ [p]}
    return c


step :: String -> (State -> Exp -> Maybe Exp) -> IO ()
step msg f = modifyState $ \s ->
    let ff = f s
        Goal pre g1:gs = goal s
        swp = if focusRhs s then sym else id
        g2 = (!! focusInd s) $
             [swp $ gen e | (e, gen) <- contextsBi $ swp g1, Just e <- [ff e]] ++
             error ("nothing matches, " ++ msg)
    in s{goal = auto s (Goal pre g2) ++ gs}

expand :: IO ()
expand = step "Eta expand" $ \_ o@(fromLams -> (vs,x)) -> Just $
    let v:_ = fresh $ vars o 
    in lams (vs ++ [v]) $ App x $ Var v

unfold :: String -> IO ()
unfold x = step ("unfold " ++ x) $ \s ->
    let rep =
            case () of
                _ | Just e <- lookup (V x) $ defined s -> \v -> if v == x then Just e else Nothing
                  | Just e <- lookup x $ types s -> \v -> Just $ Case (Var (V v))
                      [(PCon c vs, apps (Con c) (map Var vs)) | (c, n) <- e, let vs = take n $ fresh []]
                  | otherwise -> error $ "Unknown unfolding for " ++ x
    in \x -> case x of Var (V v) -> rep v; _ -> Nothing

unlet :: IO ()
unlet = step "unlet" $ \_ x ->
    case x of Let a b x -> Just $ subst [(a,b)] x; _ -> Nothing

unsafeReplace :: String -> String -> IO ()
unsafeReplace (parse -> a) (parse -> b) = step "replace" $ \_ x ->
    if x == a then Just b else Nothing

auto :: State -> Goal -> [Goal]
auto s = f full
    where
        full = [autoSimplify, autoLaw s, autoPeelCase, autoPeelCon, autoPeelVar]

        f [] g = [g]
        f (x:xs) g = case x g of
            Nothing -> f xs g
            Just [g2] | g == g2 -> f xs g
            Just gs -> concatMap (f full) gs


autoSimplify :: Goal -> Maybe [Goal]
autoSimplify (Goal pre x) = Just [Goal pre $ simplifyProp x]

autoLaw :: State -> Goal -> Maybe [Goal]
autoLaw s (Goal pre x)
    | tautology x = Just []
    | any (==> x) (pre ++ proved s) = Just []
    | otherwise = Nothing

autoPeelCase :: Goal -> Maybe [Goal]
autoPeelCase (Goal pre (Prop vs a b))
    | pattern a =^= pattern b = Just $ zipWith (\a b -> Goal pre $ Prop vs a b) (split a) (split b)
    | otherwise = Nothing
    where
        -- distinguishes the salient features
        pattern (Case on alts) = Just (on, map (patCon . fst) alts)
        pattern x = Nothing

        split (Case on alts) = [lams (patVars p) $ f on p x | (p,x) <- alts]
            where f (Var on) (PCon c vs) | on `notElem` vs = Let on (apps (Con c) (map Var vs))
                  f _ _ = id

autoPeelCon :: Goal -> Maybe [Goal]
autoPeelCon (Goal pre (Prop vs a b))
    | pattern a =^= pattern b = Just $ zipWith (\a b -> Goal pre $ Prop vs a b) (split a) (split b)
    | otherwise = Nothing
    where
        pattern (fromApps -> (Con ctr, args)) = Just (ctr, length args)
        pattern x = Nothing

        split (fromApps -> (Con ctr, args)) = map (lams vs) args

autoPeelVar :: Goal -> Maybe [Goal]
autoPeelVar (Goal pre (Prop vs a b))
    | pattern a =^= pattern b = Just $ zipWith (\a b -> Goal pre $ Prop vs a b) (split a) (split b)
    | otherwise = Nothing
    where
        pattern (fromApps -> (Var v, args)) | v `elem` vs = Just (v, length args)
        pattern x = Nothing

        split (fromApps -> (Var v, args)) = args

{-

autoRemoveLam :: IO ()
autoRemoveLam = modifyState $ \s -> s{goal = [Goal pre $ f x | Goal pre x <- goal s]}
    where
        f (a :=: b) | unused <- pattern a `intersect` pattern b = split unused a :=: split unused b

        pattern (fromLams -> (vs, x)) = [i | (i,v) <- zip [0..] vs, v `notElem` free x]
        split unused (fromLams -> (vs, x)) = lams [v | (i,v) <- zip [0..] vs, i `notElem` unused] x
-}

recurse :: IO ()
recurse = modifyState $ \s ->
    let Goal pre p@(Prop vs a b):gs = goal s
    in case (reduce s a, reduce s b) of
        (Nothing, Nothing) -> error $ "Cannot reduce\n" ++ pretty a ++ "\n" ++ pretty b
        (aa, bb) -> s{goal = auto s (Goal (p:pre) $ Prop vs (fromMaybe a aa) (fromMaybe b bb)) ++ gs}

reduce :: State -> Exp -> Maybe Exp
reduce State{..} = f
    where
        f (Lam v x) = Lam v <$> f x
        f (App a b) = (`App` b) <$> f a
        f (Var v) = lookup v defined
        f (Case x xs) = (`Case` xs) <$> f x
        f x = error $ "step: Don't know, " ++ pretty x

divide :: IO ()
divide = modifyState $ \s ->
    let Goal pre (Prop vs a b):gs = goal s in
    case (f a, f b) of
        (Just (oa, ca), Just (ob, cb)) | oa == ob, length ca == length cb ->
            s{goal = concat (zipWith (\a b -> auto s $ Goal pre $ Prop vs a b) ca cb) ++ gs}
    where
        z = Var $ V ""
        f (App a b) = Just (App z z, [a,b])
        f _ = Nothing
