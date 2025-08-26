module Subtyping.Recursive.Lib (SubtypingResult (..)) where

import Syntax (Typ (..))
import Lib (Derivation (..))


data SubtypingResult = SubtypingResult
  { isSubtype :: Bool
  , leftType :: Typ
  , rightType :: Typ
  , subtypingDerivation :: [Derivation]
  , subtypingErrorMsg :: Maybe String
  }