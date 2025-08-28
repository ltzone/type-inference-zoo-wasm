module Opt (Option (..), options) where

import System.Console.GetOpt

data Option = Typing String | Subtyping String | Meta
  deriving (Eq, Show)

options :: [OptDescr Option]
options =
  [Option [] ["typing"] (ReqArg Typing "TYPING_ALG_NAME") "TYPING_ALG_NAME"
  ,Option [] ["subtyping"] (ReqArg Subtyping "SUBTYPING_MODE") "SUBTYPING_MODE (e.g., 'nominal')"
  ,Option [] ["meta"] (NoArg Meta) "Output algorithm metadata as JSON"
  ]
