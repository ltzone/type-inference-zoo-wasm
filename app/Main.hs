{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Alg
import Data.Foldable (find)
import Lib (InferResult (..), toJson)
import Opt (Option (..), options)
import Parser (parseTrm, parseTyp)
import Syntax (Trm, Typ)
import System.Console.GetOpt (ArgOrder (Permute), getOpt)
import System.Environment (getArgs)

runTyping :: String -> Trm -> String
runTyping algName tm = case algName of
  "W" -> toJson $ runAlgW tm
  "R" -> toJson $ runAlgR tm
  "DK" -> toJson $ runDK tm
  "Worklist" -> toJson $ runWorklist tm
  "Elementary" -> toJson $ runElementary tm
  "Bounded" -> toJson $ runBounded tm
  "IU" -> toJson $ runIU tm
  "Contextual" -> toJson $ runContextual tm
  _ -> toJson $ InferResult False Nothing [] (Just $ "Invalid algorithm: " ++ algName) False

runSubtyping :: String -> Typ -> Typ -> String
runSubtyping mode lty rty = case mode of
  "nominal" -> toJson $ runNominalSubtyping lty rty
  _ -> toJson $ InferResult False Nothing [] (Just $ "Invalid subtyping mode: " ++ mode) False

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (flags, [code], [])
      | Just (Typing algName) <- find (\case Typing _ -> True; _ -> False) flags -> do
          case parseTrm code of
            Left err -> putStrLn $ toJson $ InferResult False Nothing [] (Just err) False
            Right tm -> putStrLn $ runTyping algName tm
    (flags, [source, target], [])
      | Just (Subtyping mode) <- find (\case Subtyping _ -> True; _ -> False) flags -> do
          case (parseTyp source, parseTyp target) of
            (Left err, _) -> putStrLn $ toJson $ InferResult False Nothing [] (Just err) False
            (_, Left err) -> putStrLn $ toJson $ InferResult False Nothing [] (Just err) False
            (Right src, Right tgt) ->
              putStrLn $ runSubtyping mode src tgt
    (_, _, errs) -> print errs
