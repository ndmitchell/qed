{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Main(main) where

import Proofy
import Util


main = run $ do
    define "data Nil_ a = Nil_ | Cons_ a [a]"
    define "($) f x = f x"
    define "(.) f g x = f (g x)"
    define "(++) x y = case x of [] -> y; a:b -> a : (b ++ y)"
    define "id x = x"
    define "map f xs = case xs of [] -> []; x:xs -> f x : map f xs"
    define "foldr f z xs = case xs of [] -> z; x:xs -> f x (foldr f z xs)"
    define "foldl f z xs = case xs of [] -> z; x:xs -> foldl f (f z x) xs"
    define "head x = case x of [] -> bottom; x:xs -> x"
    define "flip f x y = f y x"
    define "last x = case x of [] -> bottom; x:xs -> case xs of [] -> x; a:b -> last (a:b)"
    define "reverse = foldl (flip (:)) []"
    define "repeat x = x : repeat x"
    define "cycle x = case x of [] -> bottom; a:as -> x ++ cycle x"
    define "zipWith f xs ys = case xs of [] -> []; x:xs -> case ys of [] -> []; y:ys -> f x y : zipWith f xs ys"
    define "zip xs ys = case xs of [] -> []; x:xs -> case ys of [] -> []; y:ys -> (x, y) : zip xs ys"
    define "(&&) x y = case x of True -> y; False -> False"
    define "not x = case x of True -> False; False -> True"
    define "catMaybes xs = case xs of [] -> []; x:xs -> case x of Nothing -> catMaybes xs; Just x -> x : catMaybes xs"
    define "filter f xs = case xs of [] -> []; x:xs -> if f x then x : filter f xs else filter f xs"
    define "isJust x = case x of Nothing -> False; Just x -> True"
    define "fromJust x = case x of Nothing -> bottom; Just x -> x"
    define "mapMaybe f xs = case xs of [] -> []; x:xs -> let rs = mapMaybe f xs in case f x of Nothing -> rs; Just r -> r:rs"
    define "fst x = case x of (a,b) -> a"
    define "snd x = case x of (a,b) -> b"
    define "uncurry f p = f (fst p) (snd p)"
    define "iterate f x = x : iterate f (f x)"
    define "concatMap f xs = concat (map f xs)"
    define "concat = foldr (++) []"
    define "maybeToList x = case x of Nothing -> []; Just x -> [x]"

    proof "\\x -> [] ++ x" "\\x -> x" $ do
        unfold "++"

    proof "\\x -> x ++ []" "\\x -> x" $ do
        recurse
        rhs $ unfold "[]"

    proof "\\x y z -> (x ++ y) ++ z" "\\x y z -> x ++ (y ++ z)" $ do
        recurse
        unfold "++"
        rhs $ unfold "++"

    proof "map id" "id" $ do
        expand
        rhs $ unfold "id"
        recurse
        unfold "id"
        rhs $ unfold "[]"

    proof "\\f g x -> map f (map g x)" "\\f g x -> map (f . g) x" $ do
        unfold "."
        recurse
        unfold "map"

    proof "\\f g -> map f . map g" "\\f g -> map (f . g)" $ do
        unfold "."
        twice unlet
        rhs expand

    proof "\\f -> (($) . f)" "\\f -> f" $ do
        unfold "$"
        unfold "."
        unlet
        twice $ rhs expand

    proof "\\f z g x -> foldr f z (map g x)" "\\f z g x -> foldr (f . g) z x" $ do
        unfold "."
        recurse
        unfold "map"

    proof "\\x -> head (reverse x)" "\\x -> last x" $ do
        unfold "head"
        unfold "reverse"
        recurse
        unlet
        unfold "foldl"
        unlet
        unfold "flip"
        unsafeReplace "flip (:) [] a" "a"
        recurse
        unlet
        unfold "flip"
        unsafeReplace "flip (:) a b" "a"

    proof "\\x -> cycle [x]" "repeat" $ do
        rhs expand
        recurse
        unlet
        twice $ unfold "++"

    proof "\\f x -> zipWith f (repeat x)" "\\f x -> map (f x)" $ do
        expand
        rhs expand
        recurse
        unlet
        unfold "repeat"

    proof "\\x y -> if x then False else y" "\\x y -> not x && y" $ do
        unfold "&&"
        unfold "not"

    proof "map fromJust . filter isJust" "catMaybes" $ do
        rhs expand
        unfold "."
        unfold "map"
        unlet
        recurse
        unfold "isJust"
        unfold "fromJust"
        unfold "map"

    proof "mapMaybe id" "catMaybes" $ do
        expand
        rhs expand
        recurse
        unfold "id"

    proof "\\f x -> map f (repeat x)" "\\f x -> repeat (f x)" $ do
        recurse
        unfold "repeat"
        unlet

    proof "\\f x y -> map (uncurry f) (zip x y)" "\\f x y -> zipWith f x y" $ do
        recurse
        unlet
        unfold "zip"
        unfold "uncurry"
        unlet
        unfold "fst"
        unfold "snd"

    proof "iterate id" "repeat" $ do
        expand
        rhs expand
        recurse
        ind 1 $ unfold "id"

    proof "\\f x -> catMaybes (map f x)" "\\f x -> mapMaybe f x" $ do
        recurse
        unfold "map"

    proof "concatMap maybeToList" "catMaybes" $ do
        unfold "concatMap"
        unfold "concat"
        rhs expand
        recurse
        unfold "map"
        unfold "++"
        unfold "maybeToList"
        unfold "++"

    proof "\\f g x -> concatMap f (map g x)" "\\f g x -> concatMap (f . g) x" $ do
        twice $ unfold "concatMap"
        twice $ unfold "concat"
        divide
