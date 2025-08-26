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

runAlg :: String -> Trm -> String
runAlg algName tm = case algName of
  "W" -> toJson $ runAlgW tm
  "R" -> toJson $ runAlgR tm
  "DK" -> toJson $ runDK tm
  "Worklist" -> toJson $ runWorklist tm
  "Elementary" -> toJson $ runElementary tm
  "Bounded" -> toJson $ runBounded tm
  "IU" -> toJson $ runIU tm
  "Contextual" -> toJson $ runContextual tm
  _ -> toJson $ InferResult False Nothing [] (Just $ "Invalid algorithm: " ++ algName) False

-- Mode switching function for subtyping algorithms (unified interface)
runSubtyping :: String -> Typ -> Typ -> String
runSubtyping mode lty rty = case mode of
  "nominal" -> toJson $ runNominalSubtyping lty rty
  "translate" -> toJson $ runDistributiveSubtyping lty rty
  _ -> toJson $ InferResult False Nothing [] (Just $ "Invalid subtyping mode: " ++ mode) False

runTranslation :: String -> Typ -> String
runTranslation mode ty = case mode of
  "standard" -> toJson $ runTranslationS ty
  _ -> toJson $ InferResult False Nothing [] (Just $ "Invalid translation mode: " ++ mode) False



main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (flags, [code], [])
      | Just (Alg algName) <- find (\case Alg _ -> True; _ -> False) flags -> do
          case parseTrm code of
            Left err -> putStrLn $ toJson $ InferResult False Nothing [] (Just err) False
            Right tm -> putStrLn $ runAlg algName tm
      | Just (Translate mode) <- find (\case Translate _ -> True; _ -> False) flags -> do
          case parseTyp code of
            Left err -> putStrLn $ toJson $ InferResult False Nothing [] (Just err) False
            Right ty -> putStrLn $ runTranslation mode ty
    (flags, [source, target], [])
      | Just (Subtyping mode) <- find (\case Subtyping _ -> True; _ -> False) flags -> do
          case (parseTyp source, parseTyp target) of
            (Left err, _) -> putStrLn $ toJson $ InferResult False Nothing [] (Just err) False
            (_, Left err) -> putStrLn $ toJson $ InferResult False Nothing [] (Just err) False
            (Right src, Right tgt) ->
              putStrLn $ runSubtyping mode src tgt
    (_, _, errs) -> print errs
