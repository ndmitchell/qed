{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Main(main) where

import Core
import Sugar


main = do
    ctors "[]" [("[]",0),(":",2)]
    defineP "." "\\f g x -> f (g x)"
    defineP "++" "\\x y -> case x of [] -> y; a:b -> a : (b ++ y)"
    defineP "id" "\\x -> x"
    defineP "map" "\\f xs -> case xs of [] -> []; x:xs -> f x : map f xs"

    goalP "\\x -> [] ++ x" "\\x -> x"
    unfold "++"
    simples
    eq

    goalP "\\x -> x ++ []" "\\x -> x"
    unfold "++"
    simples
    rhs $ split "[]"
    simples
    peelCase
    eq
    peelCtor
    eq
    induct
    eq

    goalP "\\x y z -> (x ++ y) ++ z" "\\x y z -> x ++ (y ++ z)"
    unfold "++" >> simples
    unfold "++" >> simples
    rhs $ unfold "++" >> simples
    rhs $ unfold "++" >> simples >> simples
    peelCase
    peelCase
    eq
    eq
    peelCtor
    eq
    relam [1,4,5,2,3]
    induct
    eq

    goalP "map id" "id"
    unfold "map"
    simples
    rhs $ unfold "id"
    rhs $ split "[]"
    simples
    peelCase
    peelCtor
    peelCtor
    unfold "id" >> simples >> eq
    induct
    unfold "id" >> simples >> eq

    goalP "\\f g -> map f . map g" "\\f g -> map (f . g)"
    unfold "." >> simples
    unfold "map"
    unfoldEx 1 "map" >> simples
    rhs $ unfold "map" >> simples
    rhs $ unfold "." >> simples
    simples
    peelCase
    eq
    peelCtor
    eq
    dump
