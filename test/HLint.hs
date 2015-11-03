
module HLint(hlint) where

import Proof.QED
import Control.Monad.IO.Class

hlint = do
    decl "data Nat = S Nat | Z"
    decl "data Int = Neg Nat | Zero | Pos Nat"

    skip $ prove "n x => take n (repeat x) = replicate n x" $ do
        unfold "replicate"

    skip $ prove "n x => head (drop n x) = x !! n" $ do
        unfold "head"
        unfold "error"
        recurse


    prove "f => (($) . f) = f" $ do
        unfold "$"
        unfold "."
        unlet
        twice $ rhs expand

    prove "f z g x => foldr f z (map g x) = foldr (f . g) z x" $ do
        unfold "."
        recurse
        unfold "map"

    prove "(\\x -> cycle [x]) = repeat" $ do
        rhs expand
        recurse
        unlet
        twice $ unfold "++"

    prove "f x => zipWith f (repeat x) = map (f x)" $ do
        expand
        rhs expand
        recurse
        unlet
        unfold "repeat"

    prove "x y => (if x then False else y) = not x && y" $ do
        many unfold_

    skip $ prove "map fromJust . filter isJust = catMaybes" $ do
        unfold "map"
        unfold "catMaybes"
        unfold "concatMap"
        unfold "concat"
        many $ unfold "."
        unlet
        recurse
        unfold "isJust"
        unfold "fromJust"
        bhs $ unfold "map"
        unfold "++"

    prove "mapMaybe id = catMaybes" $ do
        unfold "mapMaybe"
        unfold "."
        unlet
        rhs expand
        divide
        unfold "id"
        recurse
        rhs $ strict "[]"

    prove "f x => map f (repeat x) = repeat (f x)" $ do
        recurse
        unfold "repeat"
        unlet

    prove "f x y => map (uncurry f) (zip x y) = zipWith f x y" $ do
        unfold "zip"
        recurse
        unlet
        unfold "uncurry"
        unfold "zipWith"
        unlet
        unfold "fst"
        unfold "snd"

    prove "iterate id = repeat" $ do
        expand
        rhs expand
        recurse
        at 1 $ unfold "id"

    prove "f x => catMaybes (map f x) = mapMaybe f x" $ do
        unfold "mapMaybe"
        unfold "."

    skip $ prove "concatMap maybeToList = catMaybes" $ do
        unfold "catMaybes"
        liftIO $ print "here1"
        expand
        liftIO $ print "here2"
        twice divide
        unfold "maybeToList"

    skip $ prove "f g x => concatMap f (map g x) = concatMap (f . g) x" $ do
        twice $ unfold "concatMap"
        twice $ unfold "concat"

    skip $ prove "x => head (reverse x) = last x" $ do
        unfold "head"
        unfold "reverse"
        recurse
        unlet
        bhs unfold_
        unfold "foldl"
        unlet
        unfold "flip"
        error "generalise" -- unsafeReplace "flip (:) [] a" "a"
        recurse
        unlet
        unfold "flip"
        error "generalise" -- unsafeReplace "flip (:) a b" "a"

