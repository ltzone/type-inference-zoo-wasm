module Alg.DK.Common (isAll) where

import Syntax (Typ (..))

isAll :: Typ -> Bool
isAll (TAll _) = True
isAll _ = False
