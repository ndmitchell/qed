{-# LANGUAGE PatternGuards #-}

-- | Generic utilities.
module Util(module Util, module Safe, trace) where

import Data.List
import Debug.Trace
import System.IO.Unsafe
import Safe
import System.Environment
import Data.Tuple.Extra


rlookup :: Eq a => a -> [(b,a)] -> Maybe b
rlookup x y = lookup x $ map swap y


subset x y = null $ x \\ y

fixEq f x = if x == x2 then x else fixEq f x2
    where x2 = f x


delFst :: Eq a => a -> [(a,b)] -> [(a,b)]
delFst x = filter ((/=) x . fst)

delFsts :: Eq a => [a] -> [(a,b)] -> [(a,b)]
delFsts x = filter (flip notElem x . fst)


fast = "--fast" `elem` unsafePerformIO getArgs

idempotent :: (ShowNice a, Eq a) => String -> (a -> a) -> (a -> a)
idempotent name f x0
    | fast = x1
    | x1 == x2 = x1
    | otherwise = error $ unlines
        ["START Idempotent check failed for " ++ name ++ "!"
        ,"Input:"
        ,showNice x0
        ,"After first application:"
        ,showNice x1
        ,"After second application:"
        ,showNice x2
        ,"END Idempotent check failed for " ++ name ++ "!"
        ]
    where x1 = f x0
          x2 = f x1

equivalentOn :: (ShowNice a, ShowNice b, Eq b) => (a -> b) -> String -> a -> a -> a
equivalentOn op name x y
    | fast = y
    | xx == yy = y
    | otherwise = unsafePerformIO $ do
        writeFile "error.log" $ "-- Equivalent check failed for " ++ name ++ "\n" ++ showNice x
        error $ unlines
            ["START Equivalent check failed for " ++ name ++ "!"
            ,"Input:"
            ,showNice x
            ,"Output:"
            ,showNice y
            ,"Input (reduced):"
            ,showNice xx
            ,"Output (reduced):"
            ,showNice yy
            ,"END Equivalent check failed for " ++ name ++ "!"
            ]
    where xx = op x
          yy = op y

class ShowNice a where showNice :: a -> String
