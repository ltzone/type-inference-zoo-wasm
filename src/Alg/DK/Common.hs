{-# LANGUAGE PatternSynonyms #-}

module Alg.DK.Common (isAll, isAllB, isLam) where

import Syntax (Trm (..), Typ (..), pattern TAll)

isAll :: Typ -> Bool
isAll (TAll _) = True
isAll _ = False

isAllB :: Typ -> Bool
isAllB (TAllB _ _) = True
isAllB _ = False

isLam :: Trm -> Bool
isLam (Lam _) = True
isLam _ = False