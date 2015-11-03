
module Classes(classes) where

import Proof.QED
import Control.Monad

classes = do
    lawsMonoid <- laws $ do
        law "a => a <> mempty = a"
        law "a => mempty <> a = a"
        law "a b c => a <> (b <> c) = (a <> b) <> c"

    lawsFunctor <- laws $ do
        law "fmap id = id"
        law "f g => fmap f . fmap g = fmap (f . g)"

    lawsApplicative <- laws $ do
        law "v => pure id <*> v = v"
        law "u v w => pure (.) <*> u <*> v <*> w = u <*> (v <*> w)"
        law "f x => pure f <*> pure x = pure (f x)"
        law "u y => u <*> pure y = pure ($ y) <*> u"

    lawsMonad <- laws $ do
        law "a k => return a >>= k = k a"
        law "m => m >>= return = m"
        law "m k h => m >>= (\\x -> k x >>= h) = (m >>= k) >>= h"

    prove "x => [] ++ x = x" $ do
        unfold "++"

    prove "x => x ++ [] = x" $ do
        recurse
        rhs $ strict "[]"

    prove "x y z => (x ++ y) ++ z = x ++ (y ++ z)" $ do
        recurse
        bhs $ unfold "++"

    satisfy "Monoid []" lawsMonoid $ do
        bind "mempty = []"
        bind "(<>) = (++)"

    prove "map id = id" $ do
        bhs $ unfold "id"
        expand
        recurse
        rhs $ strict "[]"

    prove "f g => map f . map g = map (f . g)" $ do
        twice $ unfold "."
        twice unlet
        rhs expand
        recurse
        unfold "map"

    satisfy "Functor []" lawsFunctor $ do
        bind "fmap = map"

    decl "return_List = (:[])"
    decl "bind_List = flip concatMap"
    let unwind = mapM_ (perhaps . many . unfold) ["return_List","bind_List","concatMap","concat","flip","."]

    when False $ prove "a k => return_List a `bind_List` k = k a" $ do
        unwind
        unfold "map"
        unfold "foldr"
        unfold "foldr"
        unfold "map"

    prove "m => m `bind_List` return_List = m" $ do
        unwind
        recurse
        unfold "map"
        rhs $ strict "[]"
        twice $ unfold "++"

    prove "m k h => m `bind_List` (\\x -> k x `bind_List` h) = (m `bind_List` k) `bind_List` h" $ do
        unwind
        divide
        recurse
        rhs $ unfold "foldr"
        rhs $ unfold "map"
        rhs $ unfold "++"
        unsafeCheat "bored"

    skip $ satisfy "Monad []" lawsMonad $ do
        bind "return = return_List"
        bind "(>>=) = bind_List"

    prove "v => return id `ap` v = v" $ do
        unfold "ap"
        unfold "liftM2"
        unfold "$"
        unsafeCheat "need laws"

{-
-- (>>=) (return id) (\ b -> (>>=) a (\ c -> return (b c)))    =    a
--       return a >>= k = k a"
-- (>>=) a (\ c -> return c))    =    a
-- a    =    a

data Monad a = Return a | forall x . Bind (Monad x) (x -> Monad a)

eval (Return a) = a
eval (Bind (Return a) f) = f a
eval 

-}

    skip $ prove "u v w => return (.) `ap` u `ap` v `ap` w = u `ap` (v `ap` w)" $ do
        replicateM_ 100 unfold_

    skip $ prove "f x => return f `ap` return x = return (f x)" $ do
        unfold "ap"
        unfold "liftM2"
        unfold "$"
        unlet
        return ()

    skip $ do
        prove "u y => u `ap` return y = return ($ y) `ap` u" $ do
            return ()

        lawsMonad <- laws $ do
            law "a k => return a >>= k = k a"
            law "m => m >>= return = m"
            law "m k h => m >>= (\\x -> k x >>= h) = (m >>= k) >>= h"

        satisfy "Applicative Monad" lawsApplicative $ do
            bind "pure = return"
            bind "(<*>) = ap"
