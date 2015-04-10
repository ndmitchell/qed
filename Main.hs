{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Main(main) where

import Proofy


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
    define "last x = case x of [] -> bottom; x:xs -> case xs of [] -> x; a:b -> last xs"
    define "reverse = foldl (flip (:)) []"

    auto simples
    auto splitCase
    auto splitCon
    auto splitVar
    auto removeLam
    auto equal

    proof "\\x -> [] ++ x" "\\x -> x" $ do
        unfold "++"

    appendNil <- proof "\\x -> x ++ []" "\\x -> x" $ do
        unfold "++"
        rhs $ unfold "[]"
        induct

    appendAssoc <- proof "\\x y z -> (x ++ y) ++ z" "\\x y z -> x ++ (y ++ z)" $ do
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

    proof "\\f z g x -> foldr f z (map g x)" "\\f z g x -> foldr (f . g) z x" $ do
        unfold "foldr" >> unfold "map" >> rhs (unfold "foldr") >> unfold "."
        induct >> unfold "."

    proof "\\f -> (($) . f)" "\\f -> f" $ do
        unfold "$" >> unfold "." >> unlet

    define "rev x y = case x of [] -> y; x:xs -> rev xs (x:y)"
    rev <- proof "reverse" "\\x -> rev x []" $ do
        acc <- proof "rev" "\\x y -> foldl (flip (:)) y x" $ do
            unfold "foldl" >> unfold "rev" >> unlet
            induct
            at 2 $ unfold "flip"
        unfold "reverse" >> apply acc
        unfold "foldl" >> rhs (unfold "foldl")

    revStrict <- proof "\\xs ys -> rev xs ys" "\\x ys -> case x of [] -> ys; x:xs -> rev (x:xs) ys" $ do
        unfold "rev" >> rhs (unfold "rev")

    define "rev2 x = case x of [] -> []; x:xs -> rev2 xs ++ [x]"

    rev2 <- proof "reverse" "rev2" $ do
        acc <- proof "\\a b -> rev a b" "\\a b -> rev2 a ++ b" $ do
            unfold "rev" >> unfold "rev2" >> unfold "++" >> unlet
            unify induct
            unify $ refold "++"
            unify $ apply appendAssoc
            at 2 $ unfold "++"
            at 2 $ unfold "++"
        error "todo"



{-
    proof "\\a b c -> last (a:b:c)" "\\a b c -> last (b:c)" $ do
        unfold "last"
-}

--    proof "\\a b c ys zs -> head (rev (a:b:c) ys)" "\\a b c ys zs -> head (rev (b:c) zs)" $ do
  --      unfold "rev"


--    goal "\\xs ys zs -> rev (x:ys) zs" "\\xs ys zs -> rev xs [] ++ ys" -- $ do

    -- unfold "++" >> unfold "rev" >> rhs (unify $ apply revStrict) >> rhs (unfold "rev")

--    goal "\\x xs -> reverse (x:xs)" "\\x xs -> reverse xs ++ [x]"
--    unify $ apply revStrict >> rhs (apply revStrict) >> apply rev >> apply rev >> unfold "++" >> unfold "rev" >> unfold "rev"  --  unfold "rev" >> unfold "++" >> rhs (unfold "rev")

--    goal "\\x y -> reverse x ++ reverse y" "\\x y -> reverse (y ++ x)"
    return ()

--    goal "\\x -> head (reverse x)" "\\x -> last x"
--    $ do
--        unfold "head" >> unfold "reverse" >> unfold "last" >> unfold "foldl" >> unfold "flip" >> unfold "foldl"
  --      return ()

