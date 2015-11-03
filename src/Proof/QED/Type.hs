{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, BangPatterns, TupleSections, PatternGuards #-}

module Proof.QED.Type(
    Known(..), Unknown(..), Goal(..), Side(..),
    QED, getKnown, qed, qedCheat,
    addDefinition, addType, addAssumed, addProved,
    Proof, getUnknown, getGoal, setFocusSide, setFocusAt,
    BadProof(..), badProof, isBadProof,
    unsafeReplaceFirstGoal, unsafeCheat,
    Bind, addBind, runBind,
    Laws(..),
    ) where

import Control.Monad.Trans.State
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Writer
import Control.Monad.Catch as C
import Control.Monad.IO.Class
import Control.Exception
import Control.DeepSeq
import Control.Monad
import Data.IORef
import Data.Typeable
import Proof.Util
import Proof.Exp.Core
import Proof.Exp.Prop
import Control.Applicative
import Data.Monoid
import Prelude

newtype Laws = Laws [Prop]
    deriving Monoid


---------------------------------------------------------------------
-- KNOWN STATE

newtype QED a = QED (StateT Known IO a)
    deriving (Functor, Applicative, Monad, MonadIO)

qed :: QED a -> IO ()
qed (QED x) = void $ execStateT x (Known [] builtinTypes [] [] False)

qedCheat :: QED a -> IO ()
qedCheat act = qed $ do
    modifyKnown $ \s -> s{cheater=True}
    act

builtinTypes :: [(String,[(Con,Int)])]
builtinTypes =
    [("[]",[(C "[]",0),(C ":",2)])]

-- | All these things are append only
data Known = Known
    {definitions :: [(Var, Exp)]
    ,types :: [(String, [(Con,Int)])]
    ,assumed :: [Prop]
    ,proved :: [Prop]
    ,cheater :: Bool
    } deriving Show

instance NFData Known where
    rnf (Known a b c d e) = rnf5 a b c d e

getKnown :: QED Known
getKnown = QED get

modifyKnown :: (Known -> Known) -> QED ()
modifyKnown f = QED $ do
    x <- get
    x <- return $ f x
    liftIO $ evaluate $ rnf x
    put x

addDefinition :: Var -> Exp -> QED ()
addDefinition a b = modifyKnown $ \s -> s{definitions = definitions s ++ [(a,b)]}

addType :: String -> [(Con,Int)] -> QED ()
addType a b = modifyKnown $ \s -> s{types = types s ++ [(a,b)]}

addAssumed :: Prop -> QED ()
addAssumed a = modifyKnown $ \s -> s{assumed = assumed s ++ [a]}

addProved :: Prop -> Proof () -> QED ()
addProved prop proof = do
    liftIO $ putStr $ show prop
    unknown <- liftIO $ newIORef $ Unknown [Goal [] prop] Nothing 0
    Proof proof <- return $ do
        proof
        unknown <- getUnknown
        unless (null $ goals $ snd unknown) $ do
            badProof $ "Did not prove goals"
    known <- QED get
    liftIO $ proof `runReaderT` (known, unknown) `C.onException` do
        print . goals =<< readIORef unknown
    modifyKnown $ \s -> s{proved = proved s ++ [prop]}
    liftIO $ putStrLn "QED\n"


---------------------------------------------------------------------
-- UNKNOWN STATE

data Unknown = Unknown
    {goals :: [Goal] -- A list of And alternatives
    ,focusSide :: Maybe Side
    ,focusAt :: Int
    } deriving Show

data Side = LHS | RHS deriving (Show,Eq)

data Goal = Goal [Prop] Prop deriving Show

instance NFData Unknown where
    rnf (Unknown a b c) = rnf3 a b c

instance NFData Side where
    rnf LHS = ()
    rnf RHS = ()

instance NFData Goal where
    rnf (Goal a b) = rnf2 a b

newtype Proof a = Proof (ReaderT (Known, IORef Unknown) IO a)
    deriving (Functor, Applicative, Monad, MonadIO, MonadThrow, MonadCatch, MonadMask)

getUnknown :: Proof (Known, Unknown)
getUnknown = Proof $ do (k,u) <- ask; liftIO $ (k,) <$> readIORef u

getGoal :: Proof (Known, Unknown, Goal)
getGoal = do
    (known, unknown) <- getUnknown
    case goals unknown of
        [] -> badProof "No goals left, proof is already complete"
        g:gs -> return (known, unknown, g)

unsafeReplaceFirstGoal :: [Goal] -> Proof ()
unsafeReplaceFirstGoal x = do
    liftIO $ evaluate $ rnf x
    (_, u) <- Proof ask
    liftIO $ modifyIORef u $ \s -> s{goals = x ++ drop 1 (goals s)}

unsafeCheat :: String -> Proof ()
unsafeCheat msg = do
    (known, _) <- getUnknown
    unless (cheater known) $ badProof "Must use qedCheat to enable cheating"
    unsafeReplaceFirstGoal []
    liftIO $ putStrLn $ "unsafeCheat: " ++ msg

setFocusSide :: Maybe Side -> Proof ()
setFocusSide x | () <- rnf x = do (_, u) <- Proof ask; liftIO $ modifyIORef u $ \s -> s{focusSide=x}

setFocusAt :: Int -> Proof ()
setFocusAt !x = do (_, u) <- Proof ask; liftIO $ modifyIORef u $ \s -> s{focusAt=x}

newtype BadProof = BadProof String deriving Typeable
instance Show BadProof where show (BadProof x) = "Bad proof: " ++ x
instance Exception BadProof

badProof :: String -> Proof a
badProof = throwM . BadProof

isBadProof :: Proof () -> Proof Bool
isBadProof act = C.catch (act >> return False) $ \BadProof{} -> return True

---------------------------------------------------------------------
-- BINDINGS

newtype Bind a = Bind (Writer [(Var,Exp)] a)
    deriving (Functor, Applicative, Monad)

addBind :: Var -> Exp -> Bind ()
addBind a b = Bind $ tell [(a,b)]

runBind :: Bind () -> [(Var,Exp)]
runBind (Bind x) = execWriter x
