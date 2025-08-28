{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Algorithms (runAlgorithmInference, runAlgorithmSubtyping, getAllAlgorithmMeta)
import Data.Foldable (find)
import Lib (InferResult (..), toJson, getAllMeta)
import Opt (Option (..), options)
import Parser (parseTrm, parseTyp)
import System.Console.GetOpt (ArgOrder (Permute), getOpt)
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (flags, [], [])
      | Meta `elem` flags -> putStrLn $ getAllMeta getAllAlgorithmMeta
    (flags, [code], [])
      | Just (Typing algName) <- find (\case Typing _ -> True; _ -> False) flags -> do
          case parseTrm code of
            Left err -> putStrLn $ toJson $ InferResult False Nothing [] (Just err) False
            Right tm -> putStrLn $ toJson $ runAlgorithmInference algName tm
    (flags, [source, target], [])
      | Just (Subtyping algName) <- find (\case Subtyping _ -> True; _ -> False) flags -> do
          case (parseTyp source, parseTyp target) of
            (Left err, _) -> putStrLn $ toJson $ InferResult False Nothing [] (Just err) False
            (_, Left err) -> putStrLn $ toJson $ InferResult False Nothing [] (Just err) False
            (Right src, Right tgt) -> putStrLn $ toJson $ runAlgorithmSubtyping algName src tgt
    (_, _, errs) -> print errs
