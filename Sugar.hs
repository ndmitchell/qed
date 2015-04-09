{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Sugar(module Sugar) where

import Core
import Exp

defineP :: String -> String -> IO ()
defineP a b = define a (parse b)

goalP :: String -> String -> IO Equal
goalP a b = goal (parse a) (parse b)

askP :: String -> IO Equal
askP = ask . parse
