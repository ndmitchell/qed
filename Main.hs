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

    goal "\\x -> [] ++ x" "\\x -> x"
    unfold "++"

    goal "\\x -> x ++ []" "\\x -> x"
    unfold "++"
    rhs $ unfold "[]"
    induct

    goal "\\x y z -> (x ++ y) ++ z" "\\x y z -> x ++ (y ++ z)"
    unfold "++"
    unfold "++"
    rhs $ unfold "++"
    rhs $ unfold "++"
    induct

    goal "map id" "id"
    unfold "map"
    rhs $ unfold "id"
    rhs $ unfold "[]"
    unfold "id"
    induct
    unfold "id"

    g <- goal "\\f g x -> map f (map g x)" "\\f g -> map (\\x -> f (g x))"
    unfold "map"
    unfold "map"
    rhs $ unfold "map"
    induct

    goal "\\f g -> map f . map g" "\\f g -> map (f . g)"
    unfold "."
    unfold "."
    unfold "map"
    unfold "map"
    rhs $ unfold "map"
    apply g
