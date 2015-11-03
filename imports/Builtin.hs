module Builtin where

error x = bottom

bottom = bottom


-- | The Monoid that is lawful, normalising, but no more
(<>) = (++)
mempty = []

newtype Identity a = Identity a

return = Identity
a >>= b = case a of Identity a -> b a
