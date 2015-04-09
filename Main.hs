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
    peelCase
    peelCtor
    simples
    induct
    simples

    goalP "\\x y z -> (x ++ y) ++ z" "\\x y z -> x ++ (y ++ z)"
    unfold "++" >> simples
    unfold "++" >> simples
    rhs $ unfold "++" >> simples
    rhs $ unfold "++" >> simples >> simples
    peelCase
    peelCtor
    relam [1,4,5,2,3]
    induct
    simples

    goalP "map id" "id"
    unfold "map"
    simples
    rhs $ unfold "id"
    rhs $ split "[]"
    simples
    peelCase
    peelCtor
    unfold "id" >> simples
    induct
    unfold "id" >> simples

    goalP "\\f g -> map f . map g" "\\f g -> map (f . g)"
    unfold "." >> simples
    unfold "map"
    unfoldEx 1 "map" >> simples
    rhs $ unfold "map" >> simples
    rhs $ unfold "." >> simples
    simples
    peelCase
    peelCtor
    dump
