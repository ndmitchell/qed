module List ( 
    elemIndex, elemIndices,
    find, findIndex, findIndices,
    nub, nubBy, delete, deleteBy, (\\), deleteFirstsBy,
    union, unionBy, intersect, intersectBy,
    intersperse, transpose, partition, group, groupBy,
    inits, tails, isPrefixOf, isSuffixOf,
    mapAccumL, mapAccumR,
    sort, sortBy, insert, insertBy, maximumBy, minimumBy,
    genericLength, genericTake, genericDrop,
    genericSplitAt, genericIndex, genericReplicate,
    zip4, zip5, zip6, zip7,
    zipWith4, zipWith5, zipWith6, zipWith7,
    unzip4, unzip5, unzip6, unzip7, unfoldr,

    -- ...and what the Prelude exports
    -- []((:), []), -- This is built-in syntax
    map, (++), concat, filter,
    head, last, tail, init, null, length, (!!),
    foldl, foldl1, scanl, scanl1, foldr, foldr1, scanr, scanr1,
    iterate, repeat, replicate, cycle,
    take, drop, splitAt, takeWhile, dropWhile, span, break,
    lines, words, unlines, unwords, reverse, and, or,
    any, all, elem, notElem, lookup,
    sum, product, maximum, minimum, concatMap, 
    zip, zip3, zipWith, zipWith3, unzip, unzip3
    ) where

import Maybe( listToMaybe )

instance Monoid a where
  mempty = []
  mappend = (++)

infix 5 \\

elemIndex               :: Eq a => a -> [a] -> Maybe Int
elemIndex x             =  findIndex (x ==)
        
elemIndices             :: Eq a => a -> [a] -> [Int]
elemIndices x           =  findIndices (x ==)
                        
find                    :: (a -> Bool) -> [a] -> Maybe a
find p                  =  listToMaybe . filter p

findIndex               :: (a -> Bool) -> [a] -> Maybe Int
findIndex p             =  listToMaybe . findIndices p

findIndices             :: (a -> Bool) -> [a] -> [Int]
findIndices p xs        =  [ i | (x,i) <- zip xs [0..], p x ]

nub                     :: Eq a => [a] -> [a]
nub                     =  nubBy (==)

nubBy                   :: (a -> a -> Bool) -> [a] -> [a]
nubBy eq x = case x of
  []             ->  []
  (x:xs)         ->  x : nubBy eq (filter (\y -> not (eq x y)) xs)

delete                  :: Eq a => a -> [a] -> [a]
delete                  =  deleteBy (==)

deleteBy                :: (a -> a -> Bool) -> a -> [a] -> [a]
deleteBy eq x ys = case ys of
  []        -> []
  (y:ys)    -> if x `eq` y then ys else y : deleteBy eq x ys

(\\)                    :: Eq a => [a] -> [a] -> [a]
(\\)                    =  foldl (flip delete)

deleteFirstsBy          :: (a -> a -> Bool) -> [a] -> [a] -> [a]
deleteFirstsBy eq       =  foldl (flip (deleteBy eq))

union                   :: Eq a => [a] -> [a] -> [a]
union                   =  unionBy (==)    

unionBy                 :: (a -> a -> Bool) -> [a] -> [a] -> [a]
unionBy eq xs ys        =  xs ++ deleteFirstsBy eq (nubBy eq ys) xs

intersect               :: Eq a => [a] -> [a] -> [a]
intersect               =  intersectBy (==)

intersectBy             :: (a -> a -> Bool) -> [a] -> [a] -> [a]
intersectBy eq xs ys    =  [x | x <- xs, any (eq x) ys]

intersperse             :: a -> [a] -> [a]
intersperse sep xs = case xs of
  []      ->  []
  x:xs -> case xs of
    [] -> [x]
    _:_ -> x : sep : intersperse sep xs

-- transpose is lazy in both rows and columns,
--       and works for non-rectangular 'matrices'
-- For example, transpose [[1,2],[3,4,5],[]]  =  [[1,3],[2,4],[5]]
-- Note that [h | (h:t) <- xss] is not the same as (map head xss)
--      because the former discards empty sublists inside xss
transpose                :: [[a]] -> [[a]]
transpose xs = case xs of
  []             -> []
  x:xss -> case x of
    [] ->  transpose xss
    (x:xs) -> (x : [h | (h:t) <- xss]) : 
                           transpose (xs : [t | (h:t) <- xss])

partition               :: (a -> Bool) -> [a] -> ([a],[a])
partition p xs          =  (filter p xs, filter (not . p) xs)

-- group splits its list argument into a list of lists of equal, adjacent
-- elements.  e.g.,
-- group "Mississippi" == ["M","i","ss","i","ss","i","pp","i"]
group                   :: Eq a => [a] -> [[a]]
group                   =  groupBy (==)

groupBy                 :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy eq xs = case xs of
  []           ->  []
  (x:xs)       ->  let o = span (eq x) xs in (x:fst o) : groupBy eq (snd o)

-- inits xs returns the list of initial segments of xs, shortest first.
-- e.g., inits "abc" == ["","a","ab","abc"]
inits                   :: [a] -> [[a]]
inits xs = case xs of
  []                ->  [[]]
  (x:xs)            ->  [[]] ++ map (x:) (inits xs)

-- tails xs returns the list of all final segments of xs, longest first.
-- e.g., tails "abc" == ["abc", "bc", "c",""]
tails                   :: [a] -> [[a]]
tails xxs = case xxs of
  []                ->  [[]]
  (_:xs)        ->  xxs : tails xs

isPrefixOf               :: Eq a => [a] -> [a] -> Bool
isPrefixOf xs ys = case xs of
  []     -> True
  x:xs -> case ys of
    [] -> False
    y:ys -> x == y && isPrefixOf xs ys

isSuffixOf              :: Eq a => [a] -> [a] -> Bool
isSuffixOf x y          =  reverse x `isPrefixOf` reverse y

mapAccumL               :: (a -> b -> (a, c)) -> a -> [b] -> (a, [c])
mapAccumL f s xs = case xs of
  []        ->  (s, [])
  (x:xs)    ->
      let s'_y = f s x in
      let s''_ys = mapAccumL f (fst s'_y) xs in
      (fst s''_ys, snd s'_y : snd s''_ys)

mapAccumR               :: (a -> b -> (a, c)) -> a -> [b] -> (a, [c])
mapAccumR f s xs = case xs of
  []        ->  (s, [])
  (x:xs)    -> 
      let s'_ys = mapAccumR f s xs in
      let s''_y = f (fst s'_ys) x in
      (fst s''_y, snd s''_y:snd s''_ys)

unfoldr                 :: (b -> Maybe (a,b)) -> b -> [a]
unfoldr f b             = case f b of
                                Nothing    -> []
                                Just ab -> case ab of (a,b) -> a : unfoldr f b

sort                    :: (Ord a) => [a] -> [a]
sort                    =  sortBy compare

sortBy                  :: (a -> a -> Ordering) -> [a] -> [a]
sortBy cmp              =  foldr (insertBy cmp) []

insert                  :: (Ord a) => a -> [a] -> [a]
insert                  = insertBy compare

insertBy                :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertBy cmp x xs = case ys of
    []       ->  [x]
    y:ys' -> case cmp x y of
        GT -> y : insertBy cmp x ys'
        EQ  -> x : ys
        LT  -> x : ys

maximumBy               :: (a -> a -> Ordering) -> [a] -> a
maximumBy cmp xs = case xs of
 []        ->  error "List.maximumBy: empty list"
 _:_ -> foldl1 (\x y -> case cmp x y of GT -> x; EQ -> y; LT -> y) xs

minimumBy               :: (a -> a -> Ordering) -> [a] -> a
minimumBy cmp xs = case xs of
  []        ->  error "List.minimumBy: empty list"
  _:_ -> foldl1 (\x y -> case cmp x y of GT -> y; EQ -> x; LT -> x) xs

genericLength           :: (Integral a) => [b] -> a
genericLength xs = case xs of
  []        ->  0
  (x:xs)    ->  1 + genericLength xs

genericTake             :: (Integral a) => a -> [b] -> [b]
genericTake n xs = case xs of
  [] -> []
  x:xs -> if n == 0 then []
          else if n > 0 then x : genericTake (n-1) xs
          else error "List.genericTake: negative argument"

genericDrop             :: (Integral a) => a -> [b] -> [b]
genericDrop n xs = if n == 0 then xs else case xs of
  [] -> []
  _:xs -> if n > 0 then genericDrop (n-1) xs else error "List.genericDrop: negative argument"

genericSplitAt          :: (Integral a) => a -> [b] -> ([b],[b])
genericSplitAt n xs = if n == 0 then ([],xs) else case xs of
    [] -> ([],[])
    x:xs -> let o = genericSplitAt (n-1) xs in
            if n > 0 then (x:fst o, snd o) else error "List.genericSplitAt: negative argument"

genericIndex            :: (Integral a) => [b] -> a -> b
genericIndex xs n = case xs of
  [] -> error "List.genericIndex: index too large"
  x:xs -> if n == 0 then x
          else if n > 0 then genericIndex xs (n-1)
          else error "List.genericIndex: negative argument"

genericReplicate        :: (Integral a) => a -> b -> [b]
genericReplicate n x    =  genericTake n (repeat x)
