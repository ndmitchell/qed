
module Main(main) where

import Classes
import HLint
import Proof.QED

-- TODO: Formalise generalise properly. Can it be done as extraction? Is strict generalisation always sufficient?
-- TODO: Write an automatic prover

-- TOTHINK: What to do about type classes? How do you prove laws about instances? How do you associate laws?
--          Add an assume to a proof?
-- TOTHINK: What do I do about things like +? Do I assume them like I do for type classes?
-- TOTHINK: Do I just state the laws and leave it at that?

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
