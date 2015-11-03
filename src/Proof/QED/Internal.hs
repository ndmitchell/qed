
module Proof.QED.Internal(
    Known(..), getKnown,
    Unknown(..), getUnknown,
    Goal(..), getGoal,
    BadProof(..), badProof, isBadProof,
    Laws(..),
    module Proof.QED.Trusted
    ) where

import Proof.QED.Type
import Proof.QED.Trusted
