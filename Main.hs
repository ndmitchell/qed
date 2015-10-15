{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Main(main) where

import Language.Haskell.Exts
import Data.Generics.Uniplate.Data
import Data.List.Extra
import Proofy

-- TODO: Source the definitions and data types from haskell98
-- TODO: Have a proof form that takes a forall, proof "x" "x ++ []" "x"
-- TODO: Formalise generalise properly. Can it be done as extraction? Is strict generalisation always sufficient?
-- TODO: Write an automatic prover

-- TOTHINK: What to do about type classes? How do you prove laws about instances? How do you associate laws?
--          Add an assume to a proof?
-- TOTHINK: What do I do about things like +? Do I assume them like I do for type classes?
-- TOTHINK: Do I just state the laws and leave it at that?

main = run $ do
    addDefine "proof/Prelude.hs"
    addDefine "proof/Maybe.hs"
    addDefine "proof/List.hs"
    addTheorem "proof/main.thm"


addDefine :: FilePath -> IO ()
addDefine file = do
    src <- readFile file
    let res = fromParseResult $ parseFileContents $ replace "..." "undefined" src
    mapM_ add $ childrenBi res
    where
        add :: Decl -> IO ()
        add x@ClassDecl{} = mapM_ add $ children x
        add x@FunBind{} = do
            putStrLn $ prettyPrint x
            define $ prettyPrint x
        add x@PatBind{} = do
            putStrLn $ prettyPrint x
            define $ prettyPrint x
        add x@DataDecl{} = define $ prettyPrint x
        add InfixDecl{} = return ()
        add InstDecl{} = return ()
        add TypeDecl{} = return ()
        add TypeSig{} = return ()
        add x = error $ "Add decl, " ++ show x



addTheorem :: FilePath -> IO ()
addTheorem = undefined
