{-# LANGUAGE DeriveDataTypeable, PatternGuards, TupleSections, ViewPatterns #-}

-- | Module for defining and manipulating expressions.
module Prop(
    Prop(..), sym, tautology, simplifyProp, (==>)
    ) where

import Exp
import Util
import Data.Data
import Data.List.Extra

data Prop = Prop [Var] Exp Exp deriving (Eq,Show,Data,Typeable)

sym :: Prop -> Prop
sym (Prop vs a b) = Prop vs b a

instance Pretty Prop where
    pretty (Prop vs a b) = "forall " ++ unwords (map fromVar vs) ++ ".\n" ++ f a ++ f b
        where f = unlines . map ("  "++) . lines . pretty


simplifyProp :: Prop -> Prop
simplifyProp = label . simple . unlam . simple
    where
        simple (Prop vs a b) = Prop vs (simplifyExp a) (simplifyExp b)

        unlam (Prop vs (Lam a1 a2) (Lam b1 b2))
            | v:_ <- fresh $ a1:b1:vs ++ vars a2 ++ vars b2
            = unlam $ Prop (v:vs) (subst [(a1,Var v)] a2) (subst [(b1,Var v)] b2)
        unlam x = x

        label (Prop vs a b) = Prop new (subst sub $ relabelAvoid (free a ++ new) a) (subst sub $ relabelAvoid (free b ++ new) b)
            where fv = nubOrd $ free a ++ free b
                  vs2 = fv `intersect` vs
                  new = take (length vs2) $ fresh $ fv \\ vs
                  sub = zip vs2 $ map Var new


-- Does the first property imply the second
(==>) :: Prop -> Prop -> Bool
(==>) a b = a == b || simplifyProp (sym a) == b

tautology :: Prop -> Bool
tautology (Prop vs a b) = a == b
