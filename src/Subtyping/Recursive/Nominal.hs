{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Subtyping.Recursive.Nominal (runRecursiveSubtyping, runRecursiveSubtypingAlg, SubtypingResult(..)) where

import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Lib (Derivation (..), InferMonad, InferResult (..), freshTVar, runInferMonad, toJson)
import Syntax (Typ (..))
import Unbound.Generics.LocallyNameless (subst, unbind)
import Parser (parseTyp)

-- Data structure for subtyping results
data SubtypingResult = SubtypingResult
  { isSubtype :: Bool
  , sourceType :: Typ
  , targetType :: Typ
  , subtypingDerivation :: [Derivation]
  , subtypingErrorMsg :: Maybe String
  }

-- Main entry point for recursive subtyping (unified interface: returns InferResult)
runRecursiveSubtyping :: Typ -> Typ -> InferResult
runRecursiveSubtyping source target =
  case runInferMonad $ do
    lift $ tell ["\\text{Recursive Subtyping: } " ++ show source ++ " <: " ++ show target]
    -- Run the subtyping algorithm
    result <- recursiveSubtyping source target
    -- Build derivation tree
    deriv <- buildDerivation source target result
    return $ SubtypingResult
      { isSubtype = result
      , sourceType = source
      , targetType = target
      , subtypingDerivation = deriv
      , subtypingErrorMsg = Nothing
      }
  of
    Left errs -> InferResult False Nothing [] (Just $ unlines errs) False
    Right (res, msgs) ->
      let infoSteps = map (\msg -> Derivation "Info" msg []) msgs
       in InferResult
            (isSubtype res)
            (Just $ show (sourceType res) ++ " <: " ++ show (targetType res))
            (infoSteps ++ subtypingDerivation res)
            (subtypingErrorMsg res)
            False

-- Core recursive subtyping algorithm
recursiveSubtyping :: Typ -> Typ -> InferMonad Bool
recursiveSubtyping source target = do
  lift $ tell ["\\text{Checking: } " ++ show source ++ " <: " ++ show target]
  
  case (source, target) of
    -- Base cases
    (_, TTop) -> do
      lift $ tell ["\\text{Top rule: } " ++ show source ++ " <: \\top"]
      return True
      
    (TInt, TInt) -> do
      lift $ tell ["\\text{Int rule: } \\texttt{Int} <: \\texttt{Int}"]
      return True
      
    (TVar v1, TVar v2) -> do
      let result = v1 == v2
      lift $ tell ["\\text{Var rule: } " ++ show v1 ++ " <: " ++ show v2 ++ " = " ++ show result]
      return result
      
    -- Function types
    (TArr s1 s2, TArr t1 t2) -> do
      lift $ tell ["\\text{Arrow rule: } " ++ show source ++ " <: " ++ show target]
      r1 <- recursiveSubtyping t1 s1  -- Contravariant in domain
      r2 <- recursiveSubtyping s2 t2  -- Covariant in codomain
      return (r1 && r2)
      
    -- Intersection types
    (TIntersection s1 s2, target) -> do
      lift $ tell ["\\text{Intersection left: } " ++ show source ++ " <: " ++ show target]
      r1 <- recursiveSubtyping s1 target
      r2 <- recursiveSubtyping s2 target
      return (r1 && r2)
      
    (source, TIntersection t1 t2) -> do
      lift $ tell ["\\text{Intersection right: } " ++ show source ++ " <: " ++ show target]
      r1 <- recursiveSubtyping source t1
      r2 <- recursiveSubtyping source t2
      return (r1 || r2)
      
    -- Recursive types
    (TRecursive sBnd, TRecursive tBnd) -> do
      lift $ tell ["\\text{Recursive rule: } " ++ show source ++ " <: " ++ show target]
      (sVar, sBody) <- unbind sBnd
      (tVar, tBody) <- unbind tBnd
      
      -- Create fresh variables for unfolding
      freshVar <- freshTVar
      let sUnfolded = subst sVar (TVar freshVar) sBody
          tUnfolded = subst tVar (TVar freshVar) tBody
      
      recursiveSubtyping sUnfolded tUnfolded
      
    -- Labeled types
    (TLabeled sLabel sBnd, TLabeled tLabel tBnd) -> do
      lift $ tell ["\\text{Labeled rule: } " ++ show source ++ " <: " ++ show target]
      -- Check if labels are compatible
      if sLabel == tLabel
        then do
          (sVar, sBody) <- unbind sBnd
          (tVar, tBody) <- unbind tBnd
          
          -- Create fresh variables for unfolding
          freshVar <- freshTVar
          let sUnfolded = subst sVar (TVar freshVar) sBody
              tUnfolded = subst tVar (TVar freshVar) tBody
          
          recursiveSubtyping sUnfolded tUnfolded
        else do
          lift $ tell ["\\text{Label mismatch: } " ++ show sLabel ++ " != " ++ show tLabel]
          return False
          
    -- Translated recursive types
    (TTranslatedMu sBnd, TTranslatedMu tBnd) -> do
      lift $ tell ["\\text{TranslatedMu rule: } " ++ show source ++ " <: " ++ show target]
      ((sTypeVar, sLabelVar), sBody) <- unbind sBnd
      ((tTypeVar, tLabelVar), tBody) <- unbind tBnd
      
      -- Create fresh variables for unfolding
      freshTypeVar <- freshTVar
      freshLabelVar <- freshTVar
      let sUnfolded = subst sTypeVar (TVar freshTypeVar) (subst sLabelVar (TVar freshLabelVar) sBody)
          tUnfolded = subst tTypeVar (TVar freshTypeVar) (subst tLabelVar (TVar freshLabelVar) tBody)
      
      recursiveSubtyping sUnfolded tUnfolded
      
    -- Default case - no subtyping relationship
    _ -> do
      lift $ tell ["\\text{No rule applies: } " ++ show source ++ " <: " ++ show target ++ " = \\text{false}"]
      return False

-- Build derivation tree for subtyping
buildDerivation :: Typ -> Typ -> Bool -> InferMonad [Derivation]
buildDerivation source target result = do
  lift $ tell ["\\text{Building derivation for } " ++ show source ++ " <: " ++ show target ++ " = " ++ show result]
  
  -- This would build a more detailed derivation tree
  -- For now, return a simple derivation
  return [Derivation
    { ruleId = "RecursiveSubtyping"
    , expression = show source ++ " <: " ++ show target ++ " = " ++ show result
    , children = []
    }]

-- Clean interface function (string inputs)
runRecursiveSubtypingAlg :: String -> String -> String
runRecursiveSubtypingAlg sourceTypeStr targetTypeStr = 
  case (parseTyp sourceTypeStr, parseTyp targetTypeStr) of
    (Left err, _) -> toJson $ InferResult False Nothing [] (Just $ "Source type parse error: " ++ err) False
    (_, Left err) -> toJson $ InferResult False Nothing [] (Just $ "Target type parse error: " ++ err) False
    (Right source, Right target) -> toJson $ runRecursiveSubtyping source target
