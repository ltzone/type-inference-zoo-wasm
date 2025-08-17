{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Alg
import Data.Foldable (find)
import Lib (InferResult(..), toJson)
import Opt (Option (..), options)
import Parser (parseTrm)
import Syntax (Trm)
import System.Console.GetOpt (ArgOrder (Permute), getOpt)
import System.Environment (getArgs)

runAlg :: String -> Trm -> String
runAlg algName tm = case algName of
  "W" -> toJson $ runAlgW tm
  _ -> toJson $ InferResult False Nothing [] (Just $ "Invalid algorithm: " ++ algName)

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (flags, [code], [])
      | Just (Alg algName) <- find (\case Alg _ -> True; _ -> False) flags -> do
          case parseTrm code of
            Left err -> putStrLn err
            Right tm -> putStrLn $ runAlg algName tm
    (_, _, errs) -> print errs
