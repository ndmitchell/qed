
module Main(main) where

-- IDEAS: Split Var and Fun? Necessary to do simple unfold proofs without Var tracking
--        Add disprove which looks for contradictions.

import Classes
import HLint
import Proof.QED

main = qed $ do
    imports "Builtin"
    imports "Prelude"
    imports "List"
    imports "Maybe"

    law "a b => a + b = b + a"
    law "a => a + 0 = a"

    classes
    hlint
