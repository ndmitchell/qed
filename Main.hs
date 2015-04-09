{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Main(main) where

import Core
import Sugar


main = do
    reset
    ctors "[]" [("[]",0),(":",2)]
    defineP "." "\\f g x -> f (g x)"
    defineP "++" "\\x y -> case x of [] -> y; a:b -> a : (b ++ y)"
    defineP "id" "\\x -> x"
    defineP "map" "\\f xs -> case xs of [] -> []; x:xs -> f x : map f xs"

    goalP "\\x -> [] ++ x" "\\x -> x"
    unfold "++"
    simples

    goalP "\\x -> x ++ []" "\\x -> x"
    unfold "++"
    simples
    rhs $ split "[]"
    simples
    splitCase
    splitCon
    simples
    induct
    simples

    goalP "\\x y z -> (x ++ y) ++ z" "\\x y z -> x ++ (y ++ z)"
    unfold "++" >> simples
    unfold "++" >> simples
    rhs $ unfold "++" >> simples
    rhs $ unfold "++" >> simples >> simples
    splitCase
    splitCon
    relam [1,4,5,2,3]
    induct
    simples

    goalP "map id" "id"
    unfold "map"
    simples
    rhs $ unfold "id"
    rhs $ split "[]"
    simples
    splitCase
    splitCon
    unfold "id" >> simples
    induct
    unfold "id" >> simples

    g <- goalP "\\f g x -> map f (map g x)" "\\f g -> map (\\x -> f (g x))"
    unfold "map"
    unfoldEx 1 "map" >> simples
    rhs $ unfold "map" >> simples
    simples
    splitCase
    splitCon
    removeLam
    induct
    simples
    unfold "map"
    rhs $ unfold "map"
    simples
    simples

    goalP "\\f g -> map f . map g" "\\f g -> map (f . g)"
    unfold "."
    unfold "."
    simples
    unfold "map"
    unfoldEx 1 "map"
    rhs $ unfold "map"
    simples >> simples
    splitCase
    splitCon
    removeLam
    apply g
    unfold "map"
    rhs $ unfold "map"
    simples >> simples
    dump
