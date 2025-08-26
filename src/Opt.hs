module Opt (Option (..), options) where

import System.Console.GetOpt

data Option = Alg String | Subtyping String | Translate String | Html
  deriving (Eq, Show)

options :: [OptDescr Option]
options =
  [Option [] ["alg"] (ReqArg Alg "ALG_NAME") "ALG_NAME"
  ,Option [] ["subtyping"] (ReqArg Subtyping "MODE") "MODE (e.g., 'nominal')"
  ,Option [] ["translate"] (ReqArg Translate "MODE") "MODE (e.g., 'standard')"
  ]
