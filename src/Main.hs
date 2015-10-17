
module Main(main) where

import Classes
import HLint
import Proof.QED

main = qed $ do
    imports "Prelude"
    imports "List"
    imports "Maybe"

    law "a b => a + b = b + a"
    law "a => a + 0 = a"

    classes
    hlint
