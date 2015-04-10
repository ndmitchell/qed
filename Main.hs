{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Main(main) where

import Proofy


main = run $ do
    define "data Nil_ a = Nil_ | Cons_ a [a]"
    define "(.) f g x = f (g x)"
    define "(++) x y = case x of [] -> y; a:b -> a : (b ++ y)"
    define "id x = x"
    define "map f xs = case xs of [] -> []; x:xs -> f x : map f xs"

    auto simples
    auto splitCase
    auto splitCon
    auto removeLam

    proof "\\x -> [] ++ x" "\\x -> x" $ do
        unfold "++"

    proof "\\x -> x ++ []" "\\x -> x" $ do
        unfold "++"
        rhs $ unfold "[]"
        induct

    proof "\\x y z -> (x ++ y) ++ z" "\\x y z -> x ++ (y ++ z)" $ do
        unfold "++"
        unfold "++"
        rhs $ unfold "++"
        rhs $ unfold "++"
        induct

    proof "map id" "id" $ do
        unfold "map"
        rhs $ unfold "id"
        rhs $ unfold "[]"
        unfold "id"
        induct
        unfold "id"

    proof "\\f g x -> map f (map g x)" "\\f g -> map (\\x -> f (g x))" $ do
        unfold "map"
        unfold "map"
        rhs $ unfold "map"
        induct

    proof "\\f g -> map f . map g" "\\f g -> map (f . g)" $ do
        unfold "."
        unfold "."
        unfold "map"
        unfold "map"
        rhs $ unfold "map"
        unify $ refold "."
        induct
        unfold "."
