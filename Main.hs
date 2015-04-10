{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Main(main) where

import Proofy
import Control.Exception


main = flip onException dump $ do
    reset
    define "data Nil_ a = Nil_ | Cons_ a [a]"
    define "(.) f g x = f (g x)"
    define "(++) x y = case x of [] -> y; a:b -> a : (b ++ y)"
    define "id x = x"
    define "map f xs = case xs of [] -> []; x:xs -> f x : map f xs"

    goal "\\x -> [] ++ x" "\\x -> x"
    unfold "++"
    simples

    goal "\\x -> x ++ []" "\\x -> x"
    unfold "++"
    rhs $ split "[]"
    simples
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
    at 1 $ unfold "map" >> simples
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

    goal "\\f g -> map f . map g" "\\f g -> map (f . g)"
    unfold "."
    unfold "."
    simples
    unfold "map"
    at 1 $ unfold "map"
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
    putStrLn "QED"
