{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Alg
import Data.Foldable (find)
import Data.Tree.View (showTree)
import Opt (Option (..), options)
import Parser (parseTrm)
import Print (showTreeHtml, toNodeInfoTree)
import Syntax (Trm)
import System.Console.GetOpt (ArgOrder (Permute), getOpt)
import System.Environment (getArgs)

runAlg :: String -> Trm -> String
runAlg algName = case algName of
  "W" -> outTree runAlgW
  "DK" -> outTree runDK
  "Worklist" -> outStr runWorklist
  "Elementary" -> outStr runElementary
  "Bounded" -> outStr runBounded
  "IU" -> outStr runIU
  "Contextual" -> outTree runContextual
  "R" -> outTree runAlgR
  _ -> error $ "Invalid algorithm: " ++ algName
  where
    outStr alg tm = case alg tm of
      Left err -> unlines err
      Right msgs -> unlines msgs
    outTree alg tm = case alg tm of
      Left err -> err
      Right tree -> showTree tree

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
