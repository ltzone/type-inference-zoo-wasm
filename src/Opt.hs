module Opt (Option (..), options) where

import System.Console.GetOpt

data Option = Alg String | Html
  deriving (Eq, Show)

options :: [OptDescr Option]
options =
  [ Option [] ["alg"] (ReqArg Alg "ALG_NAME") "ALG_NAME",
    Option [] ["html"] (NoArg Html) "Output HTML"
  ]
