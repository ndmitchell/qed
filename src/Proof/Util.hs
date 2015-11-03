{-# LANGUAGE PatternGuards #-}

-- | Generic utilities.
module Proof.Util(module Proof.Util) where

import System.IO.Unsafe
import System.Environment
import Control.DeepSeq


rnf2 a b = rnf a `seq` rnf b
rnf3 a b c = rnf a `seq` rnf b `seq` rnf c
rnf4 a b c d = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
rnf5 a b c d e = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e

headNote note (x:xs) = x
headNote note [] = error $ "headNote on [], " ++ note

fast = "--fast" `elem` unsafePerformIO getArgs

idempotent :: (Show a, Eq a) => String -> (a -> a) -> (a -> a)
idempotent name f x0
    | fast = x1
    | x1 == x2 = x1
    | otherwise = error $ unlines
        ["START Idempotent check failed for " ++ name ++ "!"
        ,"Input:"
        ,show x0
        ,"After first application:"
        ,show x1
        ,"After second application:"
        ,show x2
        ,"END Idempotent check failed for " ++ name ++ "!"
        ]
    where x1 = f x0
          x2 = f x1

equivalentOn :: (Show a, Show b, Eq b) => (a -> b) -> String -> a -> a -> a
equivalentOn op name x y
    | fast = y
    | xx == yy = y
    | otherwise = unsafePerformIO $ do
        writeFile "error.log" $ "-- Equivalent check failed for " ++ name ++ "\n" ++ show x
        error $ unlines
            ["START Equivalent check failed for " ++ name ++ "!"
            ,"Input:"
            ,show x
            ,"Output:"
            ,show y
            ,"Input (reduced):"
            ,show xx
            ,"Output (reduced):"
            ,show yy
            ,"END Equivalent check failed for " ++ name ++ "!"
            ]
    where xx = op x
          yy = op y

simpleReadsPrec :: (String -> a) -> (Int -> ReadS a)
simpleReadsPrec f _ s = [(f s, "")]
