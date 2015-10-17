
module HLint(hlint) where

import Proof.QED

hlint = do
    prove "x y => (if x then False else y) = not x && y" $ do
        many unfold_
