{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Subtyping.Recursive.Distributive where

import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Lib (Derivation (..), InferMonad, InferResult (..), freshTVar, runInferMonad, toJson)
import Syntax (Typ (..))
import Unbound.Generics.LocallyNameless (subst, unbind)
import Parser (parseTyp)

-- Data structure for subtyping results


-- Main entry point for recursive subtyping (unified interface: returns InferResult)
-- runNominalSubtyping :: Typ -> Typ -> InferResult
-- runNominalSubtyping source target =
--   case runInferMonad $ do
--     lift $ tell ["\\text{Recursive Subtyping: } " ++ show source ++ " <: " ++ show target]
--     -- Run the subtyping algorithm producing a detailed derivation
--     (result, drv) <- nominalSubDeriv source target
--     return $ SubtypingResult
--       { isSubtype = result
--       , leftType = source
--       , rightType = target
--       , subtypingDerivation = [drv]
--       , subtypingErrorMsg = Nothing
--       }
--   of
--     Left errs -> InferResult False Nothing [] (Just $ unlines errs) False
--     Right (res, msgs) ->
--       let infoSteps = map (\msg -> Derivation "Info" msg []) msgs
--        in InferResult
--             (isSubtype res)
--             (Just $ show (leftType res) ++ " <: " ++ show (rightType res))
--             (infoSteps ++ subtypingDerivation res)
--             (subtypingErrorMsg res)
--             False

-- Build derivation tree and decision simultaneously
bcdSubDeriv :: Typ -> Typ -> InferMonad (Bool, Derivation)
bcdSubDeriv a b = error "TODO: Implement BCD-style subtyping with distributive rules"

