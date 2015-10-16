{-# LANGUAGE RecordWildCards, DeriveDataTypeable, ViewPatterns #-}

module Main(main) where

import Language.Haskell.Exts hiding (parse)
import Data.Generics.Uniplate.Data
import Data.List.Extra
import Data.Tuple.Extra
import Control.Monad
import Prop
import Exp
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
            -- putStrLn $ prettyPrint x
            define $ prettyPrint x
        add x@PatBind{} = do
            -- putStrLn $ prettyPrint x
            define $ prettyPrint x
        add x@DataDecl{} = define $ prettyPrint x
        add InfixDecl{} = return ()
        add InstDecl{} = return ()
        add TypeDecl{} = return ()
        add TypeSig{} = return ()
        add x = error $ "Add decl, " ++ show x



addTheorem :: FilePath -> IO ()
addTheorem file = do
    src <- parseTheorem <$> readFile file
    forM_ src $ \x -> case x of
        Law{} -> return ()
        Prove{} -> return ()
        Proof p xs -> void $ proofProp p $ mapM_ evalStep xs

data Theorem
    = Proof Prop [Step]
    | Law String [Prop]
    | Prove String String [(String, String)]
      deriving Show

data Step = Step String deriving Show

evalStep :: Step -> IO ()
evalStep = undefined

parseTheorem :: String -> [Theorem]
parseTheorem = map f . lexer
    where
        f (a,b) = case words a of
            "forall":_ -> Proof (parseProp a) $ map parseStep b
            ["law",a] -> Law a $ map parseProp b
            ["prove",a,a2] -> Prove a a2 $ map parseEq b
            _ -> error $ "Unknown keyword, " ++ a

parseStep :: String -> Step
parseStep = Step

parseProp :: String -> Prop
parseProp x = Prop (map V $ delete "forall" $ words quant) (parse prf1) (parse $ drop 3 prf2)
    where
        (quant, '.':prf) = breakOn "." x
        (prf1, prf2) = breakOn " = " prf

parseEq :: String -> (String, String)
parseEq = both trim . second (drop 3) . breakOn " = "

lexer :: String -> [(String, [String])]
lexer = f . filter (/= "") . map (trimEnd . uncomment) . lines . replace "\t" "    "
    where
        uncomment x = maybe x fst $ stripInfix " -- " x

        f [] = []
        f (x:xs) = (x,map trimStart a) : f b
            where (a,b) = break (not . isPrefixOf " ") xs
