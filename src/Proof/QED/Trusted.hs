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
import Data.Generics.Uniplate.Data


-- | Use a new prop which is the same as the previous goal, but with any number of unfoldings
rewriteUnfold :: Prop -> Proof ()
rewriteUnfold new@(Prop nv na nb) = do
    (Known{..}, _, Goal ps (Prop ov oa ob)) <- getGoal
    checkEqual nv ov
    checkUnfold definitions oa na
    checkUnfold definitions ob nb
    unsafeReplaceFirstGoal [Goal ps new]

checkEqual a b = when (a /= b) $ fail $ "Not equal, " ++ show a ++ " vs " ++ show b

checkUnfold defs old new = unless (f old new) $ fail "Not an unfolding"
    where
        f (Var v) e | e /= Var v, Just x <- lookup v defs = e == x
        f x y = descend (const $ Var $ V "") x == descend (const $ Var $ V "") y &&
                and (zipWith f (children x) (children y))

-- | Use a new prop which is the same as the first goals prop, but with simplified/rearranged expressions
rewriteEquivalent :: Prop -> Proof ()
rewriteEquivalent new = do
    (_, _, Goal ps _) <- getGoal
    unsafeReplaceFirstGoal [Goal ps new]

-- | Apply the coinduction principle on the computation
rewriteRecurse :: Proof ()
rewriteRecurse = undefined

-- | Split the expression into multiple subexpressions
rewriteSplit :: Proof ()
rewriteSplit = undefined


-- | The first goal is a tautology
rewriteTautology :: Proof ()
rewriteTautology = do
    (Known{..}, _, Goal pre p) <- getGoal
    if tautology p || any (==> p) (pre ++ proved) then
        unsafeReplaceFirstGoal []
     else
        fail "Not a tautology"
