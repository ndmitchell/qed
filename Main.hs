{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Main(main) where

import Sugar


main = do
    resetState
    ctors "[]" [("[]",0),(":",2)]
    define "." "\\f g x -> f (g x)"
    define "++" "\\x y -> case x of [] -> y; a:b -> a : (b ++ y)"
    define "id" "\\x -> x"
    define "map" "\\f xs -> case xs of [] -> []; x:xs -> f x : map f xs"

    goal "\\x -> [] ++ x" "\\x -> x"
    unfold "++"
    simples

    goal "\\x -> x ++ []" "\\x -> x"
    unfold "++"
    simples
    rhs $ split "[]"
    splitCase
    splitCon
    simples
    induct
    simples

    goal "\\x y z -> (x ++ y) ++ z" "\\x y z -> x ++ (y ++ z)"
    unfold "++" >> simples
    unfold "++" >> simples
    rhs $ unfold "++" >> simples
    rhs $ unfold "++" >> simples >> simples
    splitCase
    splitCon
    relam [1,4,5,2,3]
    induct
    simples

    goal "map id" "id"
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

    g <- goal "\\f g x -> map f (map g x)" "\\f g -> map (\\x -> f (g x))"
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

    goal "\\f g -> map f . map g" "\\f g -> map (f . g)"
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
