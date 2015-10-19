{-# LANGUAGE RecordWildCards #-}

module Proof.QED.Trusted(
    rewriteUnfold,
    rewriteEquivalent,
    rewriteRecurse,
    rewriteSplit,
    rewriteTautology
    ) where

import Proof.Exp.Prop
import Proof.Exp.Core
import Proof.QED.Type
import Control.Monad
import Data.Maybe
import Data.Generics.Uniplate.Data


-- | Use a new prop which is the same as the previous goal, but with any number of unfoldings
rewriteUnfold :: Prop -> Proof ()
rewriteUnfold new@(Prop nv na nb) = do
    (Known{..}, _, Goal ps (Prop ov oa ob)) <- getGoal
    checkEqual nv ov
    checkUnfold definitions ov oa na
    checkUnfold definitions ov ob nb
    unsafeReplaceFirstGoal [Goal ps new]

checkEqual a b = when (a /= b) $ fail $ "Not equal, " ++ show a ++ " vs " ++ show b

checkUnfold defs vars old new = unless (f old new) $ fail $ "Trusted, invalid unfolding"
    where
        -- variables that have been captured, err on being too conservative
        vars2 = vars ++ concat [childrenBi $ descend (const $ Con $ C "") x | x <- universe old, not $ isVar x]

        f (Var v) e | e /= Var v, v `notElem` vars2, Just x <- lookup v defs = e == x
        f x y = descend (const $ Var $ V "") x == descend (const $ Var $ V "") y &&
                and (zipWith f (children x) (children y))


-- | Use a new prop which is the same as the first goals prop, but with simplified/rearranged expressions
rewriteEquivalent :: Prop -> Proof ()
rewriteEquivalent new@(Prop nv na nb) = do
    (_, _, Goal pre (Prop ov oa ob)) <- getGoal
    unsafeReplaceFirstGoal [Goal pre new]


-- | Apply the coinduction principle on the computation
rewriteRecurse :: Proof ()
rewriteRecurse = do
    (known, _, Goal pre p@(Prop vs a b)) <- getGoal
    case (reduce known a, reduce known b) of
        (Nothing, Nothing) -> fail $ "Cannot reduce\n" ++ show a ++ "\n" ++ show b
        (aa, bb) -> unsafeReplaceFirstGoal [Goal (p:pre) $ Prop vs (fromMaybe a aa) (fromMaybe b bb)]

reduce :: Known -> Exp -> Maybe Exp
reduce Known{..} = f
    where
        f (Lam v x) = Lam v <$> f x
        f (App a b) = (`App` b) <$> f a
        f (Var v) = lookup v definitions
        f (Case x xs) = (`Case` xs) <$> f x
        f x = error $ "step: Don't know, " ++ pretty x


-- | Split the expression into multiple subexpressions
rewriteSplit :: Proof ()
rewriteSplit = do
    (_, _, Goal pre (Prop vs a b)) <- getGoal
    checkEqual (descend (const $ Con $ C "") a) (descend (const $ Con $ C "") b)
    when (null $ children a) $ fail "No children to split apart"
    case (a,b) of
        (Lam v a, Lam _ b) | v `notElem` vs -> unsafeReplaceFirstGoal [Goal pre $ Prop (vs ++ [v]) a b]
        _ -> unsafeReplaceFirstGoal $ zipWith (\a b -> Goal pre $ Prop vs a b) (f a) (f b)
    where
        f (App a b) = [a,b]
        f (Case a bs) = a : map g bs
            where g (PCon c vs, e) = lams vs e
        f (Let _ a b) = [a,b]


-- | The first goal is a tautology
rewriteTautology :: Proof ()
rewriteTautology = do
    (Known{..}, _, Goal pre p) <- getGoal
    if tautology p || any (==> p) (pre ++ proved) then
        unsafeReplaceFirstGoal []
     else
        fail "Not a tautology"
