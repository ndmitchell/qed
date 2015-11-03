
module Main(main) where

import Classes
import HLint
import Proof.QED

main = qedCheat $ do
    imports "Builtin"
    imports "Prelude"
    imports "List"
    imports "Maybe"
    imports "Monad"

    law "a b => a + b = b + a"
    law "a => a + 0 = a"

    classes
    hlint
