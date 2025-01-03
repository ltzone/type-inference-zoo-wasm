module Main (main) where

import Alg
import Data.Tree.View (drawTree)
import Opt (Option (..), options)
import Parser (parseTrm)
import System.Console.GetOpt
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (flags, [code], []) | Alg "W" `elem` flags -> do
      case parseTrm code of
        Left err -> putStrLn err
        Right tm -> case runAlgW tm of
          Left err -> putStrLn err
          Right tree -> drawTree tree
    (flags, [code], []) | Alg "DK" `elem` flags -> do
      case parseTrm code of
        Left err -> putStrLn err
        Right tm -> case runDK tm of
          Left err -> putStrLn err
          Right tree -> drawTree tree
    (flags, [code], []) | Alg "Worklist" `elem` flags -> do
      case parseTrm code of
        Left err -> putStrLn err
        Right tm -> case runWorklist tm of
          Left errs -> putStrLn $ unlines errs
          Right msgs -> putStrLn $ unlines msgs
    (flags, [code], []) | Alg "Elementary" `elem` flags -> do
      case parseTrm code of
        Left err -> putStrLn err
        Right tm -> case runElementary tm of
          Left errs -> putStrLn $ unlines errs
          Right msgs -> putStrLn $ unlines msgs 
    (flags, [code], []) | Alg "Bounded" `elem` flags -> do
      case parseTrm code of
        Left err -> putStrLn err
        Right tm -> case runBounded tm of
          Left errs -> putStrLn $ unlines errs
          Right msgs -> putStrLn $ unlines msgs 
    (flags, [code], []) | Alg "IU" `elem` flags -> do
      case parseTrm code of
        Left err -> putStrLn err
        Right tm -> case runIU tm of
          Left errs -> putStrLn $ unlines errs
          Right msgs -> putStrLn $ unlines msgs
    (flags, [code], []) | Alg "Contextual" `elem` flags -> do
      case parseTrm code of
        Left err -> putStrLn err
        Right tm -> case runContextual tm of
          Left err -> putStrLn err
          Right tree -> drawTree tree
    (_, _, errs) -> print errs
