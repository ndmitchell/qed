{-# LANGUAGE DeriveDataTypeable, PatternGuards, TupleSections, ViewPatterns #-}

-- | Module for defining and manipulating expressions.
module Proof.Exp.Prop(
    Prop(..), sym, tautology, simplifyProp, (==>)
    ) where

import Proof.Exp.Core
import Proof.Util
import Data.Data
import Data.Maybe
import Data.List.Extra
import Control.DeepSeq

data Prop = Prop [Var] Exp Exp deriving (Eq,Data,Typeable)

instance NFData Prop where
    rnf (Prop a b c) = rnf3 a b c

sym :: Prop -> Prop
sym (Prop vs a b) = Prop vs b a

instance Pretty Prop where
    pretty (Prop vs a b) = "forall " ++ unwords (map fromVar vs) ++ ".\n" ++ f a ++ f b
        where f = unlines . map ("  "++) . lines . pretty

instance Read Prop where
    readsPrec = simpleReadsPrec $ \x -> case () of
        _ | (quant, x) <- fromMaybe ("",x) $ stripInfix " => " x
          , Just (a,b) <- stripInfix " = " x
          -> Prop (map V $ words quant) (parse a) (parse b)

instance Show Prop where
    show = pretty

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
(==>) a b = simplifyProp a == simplifyProp b || simplifyProp (sym a) == simplifyProp b

tautology :: Prop -> Bool
tautology (Prop vs a b) = a == b
