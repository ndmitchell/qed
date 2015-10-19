module Prelude (
    module PreludeList, module PreludeText, module PreludeIO,
    Bool(False, True),
    Maybe(Nothing, Just),
    Either(Left, Right),
    Ordering(LT, EQ, GT),
    Char, String, Int, Integer, Float, Double, Rational, IO,

--      These built-in types are defined in the Prelude, but
--      are denoted by built-in syntax, and cannot legally
--      appear in an export list.
--  List type: []((:), [])
--  Tuple types: (,)((,)), (,,)((,,)), etc.
--  Trivial type: ()(())
--  Functions: (->)

    Eq((==), (/=)),
    Ord(compare, (<), (<=), (>=), (>), max, min),
    Enum(succ, pred, toEnum, fromEnum, enumFrom, enumFromThen,
         enumFromTo, enumFromThenTo),
    Bounded(minBound, maxBound),
    Num((+), (-), (*), negate, abs, signum, fromInteger),
    Real(toRational),
    Integral(quot, rem, div, mod, quotRem, divMod, toInteger),
    Fractional((/), recip, fromRational),
    Floating(pi, exp, log, sqrt, (**), logBase, sin, cos, tan,
             asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh),
    RealFrac(properFraction, truncate, round, ceiling, floor),
    RealFloat(floatRadix, floatDigits, floatRange, decodeFloat,
              encodeFloat, exponent, significand, scaleFloat, isNaN,
              isInfinite, isDenormalized, isIEEE, isNegativeZero, atan2),
    Monad((>>=), (>>), return, fail),
    Functor(fmap),
    mapM, mapM_, sequence, sequence_, (=<<), 
    maybe, either,
    (&&), (||), not, otherwise,
    subtract, even, odd, gcd, lcm, (^), (^^), 
    fromIntegral, realToFrac, 
    fst, snd, curry, uncurry, id, const, (.), flip, ($), until,
    asTypeOf, error, undefined,
    seq, ($!)
  ) where

import PreludeBuiltin                      -- Contains all `prim' values
import UnicodePrims( primUnicodeMaxChar )  -- Unicode primitives
import PreludeList
import PreludeText
import PreludeIO
import Ratio( Rational )

infixr 9  .
infixr 8  ^, ^^, **
infixl 7  *, /, `quot`, `rem`, `div`, `mod`
infixl 6  +, -

-- The (:) operator is built-in syntax, and cannot legally be given
-- a fixity declaration; but its fixity is given by:
--   infixr 5  :

infix  4  ==, /=, <, <=, >=, >
infixr 3  &&
infixr 2  ||
infixl 1  >>, >>=
infixr 1  =<<
infixr 0  $, $!, `seq`

-- Standard types, classes, instances and related functions

-- Equality and Ordered classes


class  Eq a  where
    (==), (/=) :: a -> a -> Bool

        -- Minimal complete definition:
        --      (==) or (/=)
    x /= y     =  not (x == y)
    x == y     =  not (x /= y)


class  (Eq a) => Ord a  where
    compare              :: a -> a -> Ordering
    (<), (<=), (>=), (>) :: a -> a -> Bool
    max, min             :: a -> a -> a

        -- Minimal complete definition:
        --      (<=) or compare
        -- Using compare can be more efficient for complex types.
    compare x y = if x == y then EQ else if x <= y then LT else GT

    x <= y           =  compare x y /= GT
    x <  y           =  compare x y == LT
    x >= y           =  compare x y /= LT
    x >  y           =  compare x y == GT

-- note that (min x y, max x y) = (x,y) or (y,x)
    max x y = if x <= y then y else x
    min x y = if x <= y then x else y

-- Enumeration and Bounded classes


class  Enum a  where
    succ, pred       :: a -> a
    toEnum           :: Int -> a
    fromEnum         :: a -> Int
    enumFrom         :: a -> [a]             -- [n..]
    enumFromThen     :: a -> a -> [a]        -- [n,n'..]
    enumFromTo       :: a -> a -> [a]        -- [n..m]
    enumFromThenTo   :: a -> a -> a -> [a]   -- [n,n'..m]

        -- Minimal complete definition:
        --      toEnum, fromEnum
--
-- NOTE: these default methods only make sense for types
--   that map injectively into Int using fromEnum
--   and toEnum.
    succ             =  toEnum . (+1) . fromEnum
    pred             =  toEnum . (subtract 1) . fromEnum
    enumFrom x       =  map toEnum [fromEnum x ..]
    enumFromTo x y   =  map toEnum [fromEnum x .. fromEnum y]
    enumFromThen x y =  map toEnum [fromEnum x, fromEnum y ..]
    enumFromThenTo x y z = 
                        map toEnum [fromEnum x, fromEnum y .. fromEnum z]


class  Bounded a  where
    minBound         :: a
    maxBound         :: a

-- Numeric classes


class  (Eq a, Show a) => Num a  where
    (+), (-), (*)    :: a -> a -> a
    negate           :: a -> a
    abs, signum      :: a -> a
    fromInteger      :: Integer -> a

        -- Minimal complete definition:
        --      All, except negate or (-)
    x - y            =  x + negate y
    negate x         =  0 - x


class  (Num a, Ord a) => Real a  where
    toRational       ::  a -> Rational


class  (Real a, Enum a) => Integral a  where
    quot, rem        :: a -> a -> a   
    div, mod         :: a -> a -> a
    quotRem, divMod  :: a -> a -> (a,a)
    toInteger        :: a -> Integer

        -- Minimal complete definition:
        --      quotRem, toInteger
    n `quot` d       =  fst $ quotRem n d
    n `rem` d        =  snd $ quotRem n d
    n `div` d        =  fst $ divMod n d
    n `mod` d        =  snd $ divMod n d
    divMod n d       =  if signum r == - signum d then (q-1, r+d) else qr
                        where qr = quotRem n d
                              q = fst qr
                              r = snd qr


class  (Num a) => Fractional a  where
    (/)              :: a -> a -> a
    recip            :: a -> a
    fromRational     :: Rational -> a

        -- Minimal complete definition:
        --      fromRational and (recip or (/))
    recip x          =  1 / x
    x / y            =  x * recip y


class  (Fractional a) => Floating a  where
    pi                  :: a
    exp, log, sqrt      :: a -> a
    (**), logBase       :: a -> a -> a
    sin, cos, tan       :: a -> a
    asin, acos, atan    :: a -> a
    sinh, cosh, tanh    :: a -> a
    asinh, acosh, atanh :: a -> a

        -- Minimal complete definition:
        --      pi, exp, log, sin, cos, sinh, cosh
        --      asin, acos, atan
        --      asinh, acosh, atanh
    x ** y           =  exp (log x * y)
    logBase x y      =  log y / log x
    sqrt x           =  x ** 0.5
    tan  x           =  sin  x / cos  x
    tanh x           =  sinh x / cosh x



class  (Real a, Fractional a) => RealFrac a  where
    properFraction   :: (Integral b) => a -> (b,a)
    truncate, round  :: (Integral b) => a -> b
    ceiling, floor   :: (Integral b) => a -> b

        -- Minimal complete definition:
        --      properFraction
    truncate x       =  fst $ properFraction x
    

class  (RealFrac a, Floating a) => RealFloat a  where
    floatRadix       :: a -> Integer
    floatDigits      :: a -> Int
    floatRange       :: a -> (Int,Int)
    decodeFloat      :: a -> (Integer,Int)
    encodeFloat      :: Integer -> Int -> a
    exponent         :: a -> Int
    significand      :: a -> a
    scaleFloat       :: Int -> a -> a
    isNaN, isInfinite, isDenormalized, isNegativeZero, isIEEE
                     :: a -> Bool
    atan2            :: a -> a -> a

        -- Minimal complete definition:
        --      All except exponent, significand, 
        --                 scaleFloat, atan2
-- Numeric functions


subtract         :: (Num a) => a -> a -> a
subtract         =  flip (-)


even, odd        :: (Integral a) => a -> Bool
even n           =  n `rem` 2 == 0
odd              =  not . even




fromIntegral     :: (Integral a, Num b) => a -> b
fromIntegral     =  fromInteger . toInteger


realToFrac     :: (Real a, Fractional b) => a -> b
realToFrac      =  fromRational . toRational

-- Monadic classes


class  Functor f  where
    fmap              :: (a -> b) -> f a -> f b


class  Monad m  where
    (>>=)  :: m a -> (a -> m b) -> m b
    (>>)   :: m a -> m b -> m b
    return :: a -> m a
    fail   :: String -> m a

        -- Minimal complete definition:
        --      (>>=), return
    m >> k  =  m >>= \_ -> k
    fail s  = error s


sequence       :: Monad m => [m a] -> m [a] 
sequence       =  foldr (\p q -> p >>= \x -> q >>= \y -> return (x:y)) (return [])


sequence_      :: Monad m => [m a] -> m () 
sequence_      =  foldr (>>) (return ())

-- The xxxM functions take list arguments, but lift the function or
-- list element to a monad type

mapM             :: Monad m => (a -> m b) -> [a] -> m [b]
mapM f as        =  sequence (map f as)


mapM_            :: Monad m => (a -> m b) -> [a] -> m ()
mapM_ f as       =  sequence_ (map f as)


(=<<)            :: Monad m => (a -> m b) -> m a -> m b
f =<< x          =  x >>= f


-- Trivial type


-- data  ()  =  ()  deriving (Eq, Ord, Enum, Bounded)
-- Not legal Haskell; for illustration only

-- Function type

-- identity function

id               :: a -> a
id x             =  x

-- constant function

const            :: a -> b -> a
const x y        =  x

-- function composition

(.)              :: (b -> c) -> (a -> b) -> a -> c
f . g            =  \ x -> f (g x)

-- flip f  takes its (first) two arguments in the reverse order of f.

flip             :: (a -> b -> c) -> b -> a -> c
flip f x y       =  f y x


seq :: a -> b -> b
seq = ...       -- Primitive

-- right-associating infix application operators 
-- (useful in continuation-passing style)

($), ($!) :: (a -> b) -> a -> b
f $  x    =  f x
f $! x    =  x `seq` f x


-- Boolean type


data  Bool  =  False | True     deriving (Eq, Ord, Enum, Read, Show, Bounded)

-- Boolean functions


(&&), (||)       :: Bool -> Bool -> Bool
x && y = case x of True -> y; False -> False
x || y = case x of True -> True; False -> y

not              :: Bool -> Bool
not x = case x of True -> False; False -> True


otherwise        :: Bool
otherwise        =  True


-- Character type


-- data Char = ... 'a' | 'b' ... -- Unicode values


instance  Eq Char  where
    c == c'          =  fromEnum c == fromEnum c'


instance  Ord Char  where
    c <= c'          =  fromEnum c <= fromEnum c'


instance  Enum Char  where
    toEnum            = primIntToChar
    fromEnum          = primCharToInt
    enumFrom c        = map toEnum [fromEnum c .. fromEnum (maxBound::Char)]
    enumFromThen c c' = map toEnum [fromEnum c, fromEnum c' .. fromEnum lastChar]
                      where lastChar :: Char
                            lastChar | c' < c    = minBound
                                     | otherwise = maxBound


instance  Bounded Char  where
    minBound  =  '\0'
    maxBound  =  primUnicodeMaxChar


type  String = [Char]


-- Maybe type


data  Maybe a  =  Nothing | Just a      deriving (Eq, Ord, Read, Show)


maybe              :: b -> (a -> b) -> Maybe a -> b
maybe n f x = case x of Nothing -> n; Just x ->  f x


instance  Functor Maybe  where
    fmap f Nothing    =  Nothing
    fmap f (Just x)   =  Just (f x)
        

instance  Monad Maybe  where
    (Just x) >>= k   =  k x
    Nothing  >>= k   =  Nothing
    return           =  Just
    fail s           =  Nothing

-- Either type


data  Either a b  =  Left a | Right b   deriving (Eq, Ord, Read, Show)


either               :: (a -> c) -> (b -> c) -> Either a b -> c
either f g x = case x of Left x -> f x; Right y ->  g y

-- IO type


data IO a     -- abstract


instance  Functor IO where
   fmap f x           =  x >>= (return . f)


instance Monad IO where
   (>>=)  = ...
   return = ...
   fail s = ioError (userError s)

-- Ordering type


data  Ordering  =  LT | EQ | GT
          deriving (Eq, Ord, Enum, Read, Show, Bounded)


-- Standard numeric types.  The data declarations for these types cannot
-- be expressed directly in Haskell since the constructor lists would be
-- far too large.


data  Int 

instance  Eq       Int  where 

instance  Ord      Int  where 

instance  Num      Int  where 

instance  Real     Int  where 

instance  Integral Int  where 

instance  Enum     Int  where 

instance  Bounded  Int  where 


data  Integer  

instance  Eq       Integer  where 

instance  Ord      Integer  where

instance  Num      Integer  where

instance  Real     Integer  where

instance  Integral Integer  where

instance  Enum     Integer  where


data  Float

instance  Eq         Float  where

instance  Ord        Float  where

instance  Num        Float  where

instance  Real       Float  where

instance  Fractional Float  where

instance  Floating   Float  where

instance  RealFrac   Float  where

instance  RealFloat  Float  where


data  Double

instance  Eq         Double  where

instance  Ord        Double  where

instance  Num        Double  where

instance  Real       Double  where

instance  Fractional Double  where

instance  Floating   Double  where

instance  RealFrac   Double  where

instance  RealFloat  Double  where

-- The Enum instances for Floats and Doubles are slightly unusual.
-- The `toEnum' function truncates numbers to Int.  The definitions
-- of enumFrom and enumFromThen allow floats to be used in arithmetic
-- series: [0,0.1 .. 0.95].  However, roundoff errors make these somewhat
-- dubious.  This example may have either 10 or 11 elements, depending on
-- how 0.1 is represented.


instance  Enum Float  where
    succ x           =  x+1
    pred x           =  x-1
    toEnum           =  fromIntegral
    fromEnum         =  fromInteger . truncate   -- may overflow
    enumFrom         =  numericEnumFrom
    enumFromThen     =  numericEnumFromThen
    enumFromTo       =  numericEnumFromTo
    enumFromThenTo   =  numericEnumFromThenTo


instance  Enum Double  where
    succ x           =  x+1
    pred x           =  x-1
    toEnum           =  fromIntegral
    fromEnum         =  fromInteger . truncate   -- may overflow
    enumFrom         =  numericEnumFrom
    enumFromThen     =  numericEnumFromThen
    enumFromTo       =  numericEnumFromTo
    enumFromThenTo   =  numericEnumFromThenTo


numericEnumFrom         :: (Fractional a) => a -> [a]

numericEnumFromThen     :: (Fractional a) => a -> a -> [a]

numericEnumFromTo       :: (Fractional a, Ord a) => a -> a -> [a]

numericEnumFromThenTo   :: (Fractional a, Ord a) => a -> a -> a -> [a]
numericEnumFrom         =  iterate (+1)
numericEnumFromThen n m =  iterate (+(m-n)) n
numericEnumFromTo n m   =  takeWhile (<= m+1/2) (numericEnumFrom n)
numericEnumFromThenTo n n' m = takeWhile p (numericEnumFromThen n n')
                             where
                               p = if n' >= n then (<= m + (n'-n)/2) else (>= m + (n'-n)/2)

-- Lists


-- data  [a]  =  [] | a : [a]  deriving (Eq, Ord)
-- Not legal Haskell; for illustration only


instance Functor [] where
    fmap = map


instance  Monad []  where
    m >>= k          = concat (map k m)
    return x         = [x]
    fail s           = []

-- Tuples


--data  (a,b)   =  (a,b)    deriving (Eq, Ord, Bounded)

--data  (a,b,c) =  (a,b,c)  deriving (Eq, Ord, Bounded)
-- Not legal Haskell; for illustration only

-- component projections for pairs:
-- (NB: not provided for triples, quadruples, etc.)

fst              :: (a,b) -> a
fst (x,y)        =  x


snd              :: (a,b) -> b
snd (x,y)        =  y

-- curry converts an uncurried function to a curried function;
-- uncurry converts a curried function to a function on pairs.

curry            :: ((a, b) -> c) -> a -> b -> c
curry f x y      =  f (x, y)


uncurry          :: (a -> b -> c) -> ((a, b) -> c)
uncurry f p      =  f (fst p) (snd p)

-- Misc functions

-- until p f  yields the result of applying f until p holds.

until            :: (a -> Bool) -> (a -> a) -> a -> a
until p f x = if p x then x else until p f (f x)

-- asTypeOf is a type-restricted version of const.  It is usually used
-- as an infix operator, and its typing forces its first argument
-- (which is usually overloaded) to have the same type as the second.

asTypeOf         :: a -> a -> a
asTypeOf         =  const

-- error stops execution and displays an error message


error            :: String -> a
error            =  primError

-- It is expected that compilers will recognize this and insert error
-- messages that are more appropriate to the context in which undefined 
-- appears. 


undefined        :: a
undefined        =  error "Prelude.undefined"


infixl 9  !!
infixr 5  ++
infix  4  `elem`, `notElem`

-- Map and append

map :: (a -> b) -> [a] -> [b]
map f x = case x of [] -> []; (x:xs) -> f x : map f xs


(++) :: [a] -> [a] -> [a]
xs ++ ys = case xs of [] -> ys; (x:xs) -> x : (xs ++ ys)


filter :: (a -> Bool) -> [a] -> [a]
filter p xs = case xs of
     [] -> []
     x:xs -> if p x then x : filter p xs else  filter p xs


concat :: [[a]] -> [a]
concat xss = foldr (++) [] xss


concatMap :: (a -> [b]) -> [a] -> [b]
concatMap f = concat . map f

-- head and tail extract the first element and remaining elements,
-- respectively, of a list, which must be non-empty.  last and init
-- are the dual functions working from the end of a finite list,
-- rather than the beginning.


head             :: [a] -> a
head x = case x of
    (x:_)       ->  x
    []          ->  error "Prelude.head: empty list"


tail             :: [a] -> [a]
tail x = case x of
    (_:xs)      -> xs
    []          ->  error "Prelude.tail: empty list"


last             :: [a] -> a
last x = case x of
    [] -> error "Prelude.last: empty list"
    x:xs -> case xs of
        [] -> x
        _:_ -> last xs


init             :: [a] -> [a]
init x = case x of
    [] -> error "Prelude.init: empty list"
    x:xs -> case xs of
        [] -> []
        _:_ -> x : init xs


null             :: [a] -> Bool
null x = case x of [] -> True; (_:_) ->  False

-- length returns the length of a finite list as an Int.

length           :: [a] -> Int
length xs = case xs of
    [] -> 0
    _:l -> 1 + length l

-- List index (subscript) operator, 0-origin

(!!)                :: [a] -> Int -> a
(!!) xs n = if n < 0 then error "Prelude.!!: negative index"
       else case x of
                [] -> error "Prelude.!!: index too large"
                x:xs -> if n == 0 then x else xs !! (n-1)

-- foldl, applied to a binary operator, a starting value (typically the
-- left-identity of the operator), and a list, reduces the list using
-- the binary operator, from left to right:
--  foldl f z [x1, x2, ..., xn] == (...((z `f` x1) `f` x2) `f`...) `f` xn
-- foldl1 is a variant that has no starting value argument, and  thus must
-- be applied to non-empty lists.  scanl is similar to foldl, but returns
-- a list of successive reduced values from the left:
--      scanl f z [x1, x2, ...] == [z, z `f` x1, (z `f` x1) `f` x2, ...]
-- Note that  last (scanl f z xs) == foldl f z xs.
-- scanl1 is similar, again without the starting element:
--      scanl1 f [x1, x2, ...] == [x1, x1 `f` x2, ...]


foldl            :: (a -> b -> a) -> a -> [b] -> a
foldl f z x = case x of
    []     ->  z
    (x:xs) ->  foldl f (f z x) xs


foldl1           :: (a -> a -> a) -> [a] -> a
foldl1 f x = case x of
    [] -> error "Prelude.foldl1: empty list"
    (x:xs)  ->  foldl f x xs


scanl            :: (a -> b -> a) -> a -> [b] -> [a]
scanl f q xs     =  q : (case xs of
                            []   -> []
                            x:xs -> scanl f (f q x) xs)


scanl1           :: (a -> a -> a) -> [a] -> [a]
scanl1 f x = case x of
    [] -> []
    (x:xs)  ->  scanl f x xs

-- foldr, foldr1, scanr, and scanr1 are the right-to-left duals of the
-- above functions.


foldr            :: (a -> b -> b) -> b -> [a] -> b
foldr f z x = case x of
    []     ->  z
    (x:xs) ->  f x (foldr f z xs)


foldr1           :: (a -> a -> a) -> [a] -> a
foldr1 f x = case x of
    [] -> error "Prelude.foldr1: empty list"
    x:xs -> case xs of
        [] -> x
        _:_ -> f x (foldr1 f xs)


scanr             :: (a -> b -> b) -> b -> [a] -> [b]
scanr f q0 x = case x of
    []     ->  [q0]
    (x:xs) -> let qs = scanr f q0 xs in f x (head qs) : qs

scanr1          :: (a -> a -> a) -> [a] -> [a]
scanr1 f x = case x of
    []     ->  []
    x:xs   -> case xs of
        [] -> [x]
        _:_ -> let qs = scanr1 f xs in f x (head qs) : qs

-- iterate f x returns an infinite list of repeated applications of f to x:
-- iterate f x == [x, f x, f (f x), ...]

iterate          :: (a -> a) -> a -> [a]
iterate f x      =  x : iterate f (f x)

-- repeat x is an infinite list, with x the value of every element.

repeat           :: a -> [a]
repeat x         =  x : repeat x

-- replicate n x is a list of length n with x the value of every element

replicate        :: Int -> a -> [a]
replicate n x    =  take n (repeat x)

-- cycle ties a finite list into a circular one, or equivalently,
-- the infinite repetition of the original list.  It is the identity
-- on infinite lists.


cycle            :: [a] -> [a]
cycle xs = case xs of
    []         ->  error "Prelude.cycle: empty list"
    _:_    -> xs ++ cycle xs

-- take n, applied to a list xs, returns the prefix of xs of length n,
-- or xs itself if n > length xs.  drop n xs returns the suffix of xs
-- after the first n elements, or [] if n > length xs.  splitAt n xs
-- is equivalent to (take n xs, drop n xs).


take                   :: Int -> [a] -> [a]
take n xs = if n <= 0 then  []
            else case xs of
                    [] -> []
                    x:xs -> x : take (n-1) xs


drop                   :: Int -> [a] -> [a]
drop n xs = if n <= 0 then xs
            else case xs of
                     [] -> []
                     x:xs -> drop (n-1) xs


splitAt                  :: Int -> [a] -> ([a],[a])
splitAt n xs             =  (take n xs, drop n xs)

-- takeWhile, applied to a predicate p and a list xs, returns the longest
-- prefix (possibly empty) of xs of elements that satisfy p.  dropWhile p xs
-- returns the remaining suffix.  span p xs is equivalent to 
-- (takeWhile p xs, dropWhile p xs), while break p uses the negation of p.


takeWhile               :: (a -> Bool) -> [a] -> [a]
takeWhile p xs = case xs of
    []          ->  []
    x:xs        -> if p x then  x : takeWhile p xs else []


dropWhile               :: (a -> Bool) -> [a] -> [a]
dropWhile p xs = case xs of
    []          ->  []
    x:xs' -> if p x then  dropWhile p xs' else  xs


span, break             :: (a -> Bool) -> [a] -> ([a],[a])
span p xs = case xs of
    []            -> ([],[])
    x:xs'  -> let ys_zs = span p xs'
              in if p x then (x:fst ys_zs, snd ys_zs)
                        else ([],xs)

break p                 =  span (not . p)

-- lines breaks a string up into a list of strings at newline characters.
-- The resulting strings do not contain newlines.  Similary, words
-- breaks a string up into a list of words, which were delimited by
-- white space.  unlines and unwords are the inverse operations.
-- unlines joins lines with terminating newlines, and unwords joins
-- words with separating spaces.


lines            :: String -> [String]
lines s          =  if null s then [] else let ls = break (== '\n') s
                      in  fst ls : case snd ls of
                                []      -> []
                                (_:s'') -> lines s''


words            :: String -> [String]
words s          =  let s' = dropWhile isSpace s  in
                    case s' of
                      [] -> []
                      _:_ -> let ws = break isSpace s' in
                             fst ws : words (snd ws)


unlines          :: [String] -> String
unlines          =  concatMap (++ "\n")


unwords          :: [String] -> String
unwords ws = case ws of
     []       ->  ""
     _:_ -> foldr1 (\w s -> w ++ ' ':s) ws

-- reverse xs returns the elements of xs in reverse order.  xs must be finite.

reverse          :: [a] -> [a]
reverse          =  foldl (flip (:)) []

-- and returns the conjunction of a Boolean list.  For the result to be
-- True, the list must be finite; False, however, results from a False
-- value at a finite index of a finite or infinite list.  or is the
-- disjunctive dual of and.

and, or          :: [Bool] -> Bool
and              =  foldr (&&) True
or               =  foldr (||) False

-- Applied to a predicate and a list, any determines if any element
-- of the list satisfies the predicate.  Similarly, for all.

any, all         :: (a -> Bool) -> [a] -> Bool
any p            =  or . map p
all p            =  and . map p

-- elem is the list membership predicate, usually written in infix form,
-- e.g., x `elem` xs.  notElem is the negation.

elem, notElem    :: (Eq a) => a -> [a] -> Bool
elem x           =  any (== x)
notElem x        =  all (/= x)

-- lookup key assocs looks up a key in an association list.

lookup           :: (Eq a) => a -> [(a,b)] -> Maybe b
lookup key xs = case xs of
    [] -> Nothing
    xy:xys -> case xy of
        (x,y) -> if key == x then Just y else lookup key xys

-- sum and product compute the sum or product of a finite list of numbers.

sum, product     :: (Num a) => [a] -> a
sum              =  foldl (+) 0  
product          =  foldl (*) 1

-- maximum and minimum return the maximum or minimum value from a list,
-- which must be non-empty, finite, and of an ordered type.

maximum, minimum :: (Ord a) => [a] -> a
maximum xs = case xs of
    [] -> error "Prelude.maximum: empty list"
    _:_ -> foldl1 max xs

minimum xs = case xs of
    [] ->  error "Prelude.minimum: empty list"
    _:_ -> foldl1 min xs

-- zip takes two lists and returns a list of corresponding pairs.  If one
-- input list is short, excess elements of the longer list are discarded.
-- zip3 takes three lists and returns a list of triples.  Zips for larger
-- tuples are in the List library


zip              :: [a] -> [b] -> [(a,b)]
zip              =  zipWith (,)


zip3             :: [a] -> [b] -> [c] -> [(a,b,c)]
zip3             =  zipWith3 (,,)

-- The zipWith family generalises the zip family by zipping with the
-- function given as the first argument, instead of a tupling function.
-- For example, zipWith (+) is applied to two lists to produce the list
-- of corresponding sums.


zipWith          :: (a->b->c) -> [a]->[b]->[c]
zipWith z as bs =
    case as of
        [] -> []
        a:as -> case bs of
            [] -> []
            b:bs -> z a b : zipWith z as bs


zipWith3         :: (a->b->c->d) -> [a]->[b]->[c]->[d]
zipWith3 z as bs cs = case as of
    [] -> []
    a:as -> case bs of
        [] -> []
        b:bs -> case cs of
            [] -> []
            c:cs -> z a b c : zipWith3 z as bs cs


-- unzip transforms a list of pairs into a pair of lists.  


unzip            :: [(a,b)] -> ([a],[b])
unzip            =  foldr (\ab asbs -> case ab of (a,b) -> (a:fst asbs,b:snd asbs)) ([],[])


unzip3           :: [(a,b,c)] -> ([a],[b],[c])
unzip3           =  foldr (\abc o -> case abc of (a,b,c) -> (a:fst3 o,b:snd3 o,c:thd3 o))
                          ([],[],[])

fst3 x = case x of (x,_,_) -> x
snd3 x = case x of (_,x,_) -> x
thd3 x = case x of (_,_,x) -> x


type  ReadS a  = String -> [(a,String)]

type  ShowS    = String -> String


class  Read a  where
    readsPrec        :: Int -> ReadS a
    readList         :: ReadS [a]


class  Show a  where
    showsPrec        :: Int -> a -> ShowS
    show             :: a -> String 
    showList         :: [a] -> ShowS

reads            :: (Read a) => ReadS a
reads            =  readsPrec 0


shows            :: (Show a) => a -> ShowS
shows            =  showsPrec 0


showChar         :: Char -> ShowS
showChar         =  (:)


showString       :: String -> ShowS
showString       =  (++)


showParen        :: Bool -> ShowS -> ShowS
showParen b p    =  if b then showChar '(' . p . showChar ')' else p


-- This lexer is not completely faithful to the Haskell lexical syntax.
-- Current limitations:
--    Qualified names are not handled properly
--    Octal and hexidecimal numerics are not recognized as a single token
--    Comments are not treated properly


instance  Show Int  where
    showsPrec n = showsPrec n . toInteger
        -- Converting to Integer avoids
        -- possible difficulty with minInt


instance  Read Int  where
  readsPrec p r = [(fromInteger i, t) | (i,t) <- readsPrec p r]
        -- Reading at the Integer type avoids
        -- possible difficulty with minInt


instance  Show Integer  where
    showsPrec           = showSigned showInt


instance  Read Integer  where
    readsPrec p         = readSigned readDec


instance  Show Float  where 
    showsPrec p         = showFloat
           

instance  Read Float  where
    readsPrec p         = readSigned readFloat


instance  Show Double  where
    showsPrec p         = showFloat


instance  Read Double  where
    readsPrec p         = readSigned readFloat


instance  Show ()  where
    showsPrec p () = showString "()"


instance Read () where
    readsPrec p    = readParen False
                            (\r -> [((),t) | ("(",s) <- lex r,
                                             (")",t) <- lex s ] )

instance  Show Char  where
    showsPrec p '\'' = showString "'\\''"
    showsPrec p c    = showChar '\'' . showLitChar c . showChar '\''

    showList cs = showChar '"' . showl cs
                 where showl ""       = showChar '"'
                       showl ('"':cs) = showString "\\\"" . showl cs
                       showl (c:cs)   = showLitChar c . showl cs


instance  Read Char  where
    readsPrec p      = readParen False
                            (\r -> [(c,t) | ('\'':s,t)<- lex r,
                                            (c,"\'")  <- readLitChar s])

    readList = readParen False (\r -> [(l,t) | ('"':s, t) <- lex r,
                                               (l,_)      <- readl s ])
        where readl ('"':s)      = [("",s)]
              readl ('\\':'&':s) = readl s
              readl s            = [(c:cs,u) | (c ,t) <- readLitChar s,
                                               (cs,u) <- readl t       ]


instance  (Show a) => Show [a]  where
    showsPrec p      = showList


instance  (Read a) => Read [a]  where
    readsPrec p      = readList

-- Tuples


instance  (Show a, Show b) => Show (a,b)  where
    showsPrec p (x,y) = showChar '(' . shows x . showChar ',' .
                                       shows y . showChar ')'


instance  (Read a, Read b) => Read (a,b)  where
    readsPrec p       = readParen False
                            (\r -> [((x,y), w) | ("(",s) <- lex r,
                                                 (x,t)   <- reads s,
                                                 (",",u) <- lex t,
                                                 (y,v)   <- reads u,
                                                 (")",w) <- lex v ] )

-- Other tuples have similar Read and Show instances

type  FilePath = String


data IOError    -- The internals of this type are system dependent


instance  Show IOError  where

instance  Eq IOError  where


ioError    ::  IOError -> IO a 
ioError    =   primIOError
   

userError  ::  String -> IOError
userError  =   primUserError
   

catch      ::  IO a -> (IOError -> IO a) -> IO a 
catch      =   primCatch
   

putChar    :: Char -> IO ()
putChar    =  primPutChar
   

putStr     :: String -> IO ()
putStr s   =  mapM_ putChar s
   

putStrLn   :: String -> IO ()
putStrLn s =   putStr s >> putStr "\n"
   

print      :: Show a => a -> IO ()
print x    =  putStrLn (show x)
   

getChar    :: IO Char
getChar    =  primGetChar
   

getLine    :: IO String
getLine    =  getChar >>= \c -> 
                 if c == '\n' then return "" else 
                    getLine >>= \s -> 
                       return (c:s)
            

getContents :: IO String
getContents =  primGetContents


interact    ::  (String -> String) -> IO ()
-- The hSetBuffering ensures the expected interactive behaviour
interact f  =  hSetBuffering stdin  NoBuffering >>
                  hSetBuffering stdout NoBuffering >>
                  getContents >>= \s ->
                  putStr (f s)


readFile   :: FilePath -> IO String
readFile   =  primReadFile
   

writeFile  :: FilePath -> String -> IO ()
writeFile  =  primWriteFile
   

appendFile :: FilePath -> String -> IO ()
appendFile =  primAppendFile

  -- raises an exception instead of an error


readLn :: Read a => IO a
readLn =   getLine >>= \l ->
             readIO l >>= \r ->
             return r
