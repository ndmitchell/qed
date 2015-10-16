
module Maybe(
    isJust, isNothing,
    fromJust, fromMaybe, listToMaybe, maybeToList,
    catMaybes, mapMaybe,

    -- ...and what the Prelude exports
    Maybe(Nothing, Just),
    maybe
  ) where

instance Eq a => Eq (Maybe a) where
    (==) = eqMaybe

eqMaybe x y = case x of
    Nothing -> case y of
        Nothing -> True
        Just _ -> False
    Just x -> case y of
        Nothing -> False
        Just y -> x == y

isJust                 :: Maybe a -> Bool
isJust x = case x of
    (Just a)        -> True
    Nothing         ->  False

isNothing          :: Maybe a -> Bool
isNothing          =  not . isJust

fromJust               :: Maybe a -> a
fromJust x = case x of
    (Just a)      ->  a
    Nothing       ->  error "Maybe.fromJust: Nothing"

fromMaybe              :: a -> Maybe a -> a
fromMaybe d x = case x of
    Nothing    ->  d
    Just a      ->  a

maybeToList            :: Maybe a -> [a]
maybeToList x = case x of
    Nothing -> []
    Just a -> [a]

listToMaybe            :: [a] -> Maybe a
listToMaybe = case x of
    []         ->  Nothing
    (a:_)      ->  Just a
 
catMaybes              :: [Maybe a] -> [a]
catMaybes ms           =  [ m | Just m <- ms ]
-- concatMap (\x -> case x of Nothing -> []; Just m -> [m]) ms

mapMaybe               :: (a -> Maybe b) -> [a] -> [b]
mapMaybe f             =  catMaybes . map f
