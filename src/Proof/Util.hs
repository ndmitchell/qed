{-# LANGUAGE PatternGuards #-}

-- | Generic utilities.
module Proof.Util(module Proof.Util, headNote, trace) where

import Data.List
import Debug.Trace
import System.IO.Unsafe
import Safe
import System.Environment
import Control.DeepSeq
import Data.Tuple.Extra

rnf2 a b = rnf a `seq` rnf b
rnf3 a b c = rnf a `seq` rnf b `seq` rnf c
rnf4 a b c d = rnf a `seq` rnf b `seq` rnf c `seq` rnf d

rlookup :: Eq a => a -> [(b,a)] -> Maybe b
rlookup x y = lookup x $ map swap y

Just a =^= Just b = a == b
_ =^= _ = False


subset x y = null $ x \\ y

fixEq f x = if x == x2 then x else fixEq f x2
    where x2 = f x


delFst :: Eq a => a -> [(a,b)] -> [(a,b)]
delFst x = filter ((/=) x . fst)

delFsts :: Eq a => [a] -> [(a,b)] -> [(a,b)]
delFsts x = filter (flip notElem x . fst)


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

class Pretty a where pretty :: a -> String


simpleReadsPrec :: (String -> a) -> (Int -> ReadS a)
simpleReadsPrec f _ s = [(f s, "")]
