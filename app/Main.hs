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
    (_, _, errs) -> print errs
