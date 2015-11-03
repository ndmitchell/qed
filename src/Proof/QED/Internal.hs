
module Proof.QED.Internal(
    Exp(..), Pat(..), Var(..), Con(..),
    Prop(..),
    Side(..),
    Known(..), getKnown,
    Unknown(..), getUnknown,
    Goal(..), getGoal,
    BadProof(..), badProof, isBadProof,
    Laws(..),
    module Proof.QED.Trusted
    ) where

import Proof.Exp.Core
import Proof.Exp.Prop
import Proof.QED.Type
import Proof.QED.Trusted
