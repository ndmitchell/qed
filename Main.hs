{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Main(main) where

import Core
import Sugar


main = do
    resetState
    ctors "[]" [("[]",0),(":",2)]
    defineFunctionP "." "\\f g x -> f (g x)"
    defineFunctionP "++" "\\x y -> case x of [] -> y; a:b -> a : (b ++ y)"
    defineFunctionP "id" "\\x -> x"
    defineFunctionP "map" "\\f xs -> case xs of [] -> []; x:xs -> f x : map f xs"

    addGoalP "\\x -> [] ++ x" "\\x -> x"
    unfold "++"
    simples

    addGoalP "\\x -> x ++ []" "\\x -> x"
    unfold "++"
    simples
    rhs $ split "[]"
    splitCase
    splitCon
    simples
    induct
    simples

    addGoalP "\\x y z -> (x ++ y) ++ z" "\\x y z -> x ++ (y ++ z)"
    unfold "++" >> simples
    unfold "++" >> simples
    rhs $ unfold "++" >> simples
    rhs $ unfold "++" >> simples >> simples
    splitCase
    splitCon
    relam [1,4,5,2,3]
    induct
    simples

    addGoalP "map id" "id"
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

    g <- addGoalP "\\f g x -> map f (map g x)" "\\f g -> map (\\x -> f (g x))"
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

    addGoalP "\\f g -> map f . map g" "\\f g -> map (f . g)"
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
