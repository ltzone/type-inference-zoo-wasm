{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Subtyping.Recursive.Nominal (runNominalSubtyping, runNominalSubtypingAlg, SubtypingResult(..)) where

import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Lib (Derivation (..), InferMonad, InferResult (..), freshTVar, runInferMonad, toJson)
import Syntax (Typ (..))
import Unbound.Generics.LocallyNameless (subst, unbind)
import Parser (parseTyp)

-- Data structure for subtyping results
data SubtypingResult = SubtypingResult
  { isSubtype :: Bool
  , leftType :: Typ
  , rightType :: Typ
  , subtypingDerivation :: [Derivation]
  , subtypingErrorMsg :: Maybe String
  }

-- Main entry point for recursive subtyping (unified interface: returns InferResult)
runNominalSubtyping :: Typ -> Typ -> InferResult
runNominalSubtyping source target =
  case runInferMonad $ do
    lift $ tell ["\\text{Recursive Subtyping: } " ++ show source ++ " <: " ++ show target]
    -- Run the subtyping algorithm producing a detailed derivation
    (result, drv) <- nominalSubDeriv source target
    return $ SubtypingResult
      { isSubtype = result
      , leftType = source
      , rightType = target
      , subtypingDerivation = [drv]
      , subtypingErrorMsg = Nothing
      }
  of
    Left errs -> InferResult False Nothing [] (Just $ unlines errs) False
    Right (res, msgs) ->
      let infoSteps = map (\msg -> Derivation "Info" msg []) msgs
       in InferResult
            (isSubtype res)
            (Just $ show (leftType res) ++ " <: " ++ show (rightType res))
            (infoSteps ++ subtypingDerivation res)
            (subtypingErrorMsg res)
            False

-- Core recursive subtyping algorithm
nominalSubtyping :: Typ -> Typ -> InferMonad Bool
nominalSubtyping source target = do
  -- lift $ tell ["\\text{Checking: } " ++ show source ++ " <: " ++ show target]
  
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
      r1 <- nominalSubtyping t1 s1  -- Contravariant in domain
      r2 <- nominalSubtyping s2 t2  -- Covariant in codomain
      return (r1 && r2)
      
    -- Intersection types
    (TIntersection s1 s2, target) -> do
      lift $ tell ["\\text{Intersection left: } " ++ show source ++ " <: " ++ show target]
      r1 <- nominalSubtyping s1 target
      r2 <- nominalSubtyping s2 target
      return (r1 && r2)
      
    (source, TIntersection t1 t2) -> do
      lift $ tell ["\\text{Intersection right: } " ++ show source ++ " <: " ++ show target]
      r1 <- nominalSubtyping source t1
      r2 <- nominalSubtyping source t2
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
      
      nominalSubtyping sUnfolded tUnfolded
      
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
          
          nominalSubtyping sUnfolded tUnfolded
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
      
      nominalSubtyping sUnfolded tUnfolded
      
    -- Default case - no subtyping relationship
    _ -> do
      lift $ tell ["\\text{No rule applies: } " ++ show source ++ " <: " ++ show target ++ " = \\text{false}"]
      return False

-- Build derivation tree and decision simultaneously
nominalSubDeriv :: Typ -> Typ -> InferMonad (Bool, Derivation)
nominalSubDeriv source target = do
  lift $ tell ["\\text{Derive: } " ++ show source ++ " <: " ++ show target]
  case (source, target) of
    -- Top
    (_, TTop) ->
      return
        ( True
        , Derivation { ruleId = "S-top", expression = show source ++ " <: \\top", children = [] }
        )

    -- Refl on base types
    (TInt, TInt) ->
      return (True, Derivation { ruleId = "S-int", expression = "Int <: Int", children = [] })
    (TBool, TBool) ->
      return (True, Derivation { ruleId = "S-bool", expression = "Bool <: Bool", children = [] })

    -- Type variables
    (TVar v1, TVar v2) ->
      let ok = v1 == v2
       in return
            ( ok
            , Derivation
                { ruleId = "S-var"
                , expression = show (TVar v1) ++ " <: " ++ show (TVar v2)
                , children = []
                }
            )

    -- Arrows (contravariant in domain, covariant in codomain)
    (TArr s1 s2, TArr t1 t2) -> do
      (r1, d1) <- nominalSubDeriv t1 s1
      (r2, d2) <- nominalSubDeriv s2 t2
      let ok = r1 && r2
      return
        ( ok
        , Derivation
            { ruleId = "S-arrow"
            , expression = show (TArr s1 s2) ++ " <: " ++ show (TArr t1 t2)
            , children = [d1, d2]
            }
        )

    -- Intersection on the left: s1 & s2 <: t iff s1 <: t and s2 <: t
    (TIntersection s1 s2, t) -> do
      (r1, d1) <- nominalSubDeriv s1 t
      (r2, d2) <- nominalSubDeriv s2 t
      let ok = r1 && r2
      return
        ( ok
        , Derivation
            { ruleId = "S-inter-left"
            , expression = show (TIntersection s1 s2) ++ " <: " ++ show t
            , children = if r1 then [d1] else if r2 then [d2] else [d1, d2]
            }
        )
      

    -- Intersection on the right: s <: t1 & t2 iff s <: t1 or s <: t2
    (s, TIntersection t1 t2) -> do
      (r1, d1) <- nominalSubDeriv s t1
      (r2, d2) <- nominalSubDeriv s t2
      let ok = r1 && r2
      return
        ( ok
        , Derivation
            { ruleId = "S-inter-right"
            , expression = show s ++ " <: " ++ show (TIntersection t1 t2)
            , children = [d1, d2]
            }
        )

    -- Recursive types: unfold with a shared fresh variable
    (TRecursive sBnd, TRecursive tBnd) -> do
      ((sVar), sBody) <- unbind sBnd
      ((tVar), tBody) <- unbind tBnd
      a <- freshTVar
      let sUnf = subst sVar (TVar a) sBody
          tUnf = subst tVar (TVar a) tBody
          sNUnf = subst sVar (TLabel a sUnf) sBody 
          tNUnf = subst tVar (TLabel a tUnf) tBody
      (ok, d) <- nominalSubDeriv sNUnf tNUnf
      return
        ( ok
        , Derivation
            { ruleId = "S-mu"
            , expression = show (TRecursive sBnd) ++ " <: " ++ show (TRecursive tBnd)
            , children = [d]
            }
        )

    (TLabel slabel sty, TLabel rlabel rty) ->
      if slabel == rlabel
        then do
          (ok, d) <- nominalSubDeriv sty rty
          return
            ( ok
            , Derivation
                { ruleId = "S-label"
                , expression = show (TLabel slabel sty) ++ " <: " ++ show (TLabel rlabel rty)
                , children = [d]
                }
            )
        else
          return
            ( False
            , Derivation
                { ruleId = "S-fail"
                , expression = "label mismatch: " ++ show (TLabel slabel sty) ++ " </: " ++ show (TLabel rlabel rty)
                , children = []
                }
            )


    -- the below two types should actually never appear in nominal subtyping

    -- Labeled recursive types: labels must match, then unfold together
    (TLabeled sLabel sBnd, TLabeled tLabel tBnd) ->
      if sLabel == tLabel
        then do
          (sVar, sBody) <- unbind sBnd
          (tVar, tBody) <- unbind tBnd
          a <- freshTVar
          let sUnf = subst sVar (TVar a) sBody
              tUnf = subst tVar (TVar a) tBody
          (ok, d) <- nominalSubDeriv sUnf tUnf
          return
            ( ok
            , Derivation
                { ruleId = "S-labeled"
                , expression = show (TLabeled sLabel sBnd) ++ " <: " ++ show (TLabeled tLabel tBnd)
                , children = [d]
                }
            )
        else
          return
            ( False
            , Derivation
                { ruleId = "S-fail"
                , expression = "label mismatch: " ++ show (TLabeled sLabel sBnd) ++ " </: " ++ show (TLabeled tLabel tBnd)
                , children = []
                }
            )

    -- Translated mu with a type and a label variable; unfold both with shared fresh vars
    (TTranslatedMu sBnd, TTranslatedMu tBnd) -> do
      ((sTypeVar, sLabelVar), sBody) <- unbind sBnd
      ((tTypeVar, tLabelVar), tBody) <- unbind tBnd
      a <- freshTVar
      b <- freshTVar
      let sUnf = subst sTypeVar (TVar a) (subst sLabelVar (TVar b) sBody)
          tUnf = subst tTypeVar (TVar a) (subst tLabelVar (TVar b) tBody)
      (ok, d) <- nominalSubDeriv sUnf tUnf
      return
        ( ok
        , Derivation
            { ruleId = "S-transmu"
            , expression = show (TTranslatedMu sBnd) ++ " <: " ++ show (TTranslatedMu tBnd)
            , children = [d]
            }
        )

    -- Failure
    _ ->
      return
        ( False
        , Derivation
            { ruleId = "S-fail"
            , expression = show source ++ " </: " ++ show target
            , children = []
            }
        )

-- Legacy boolean-only checker retained for logging compatibility
-- but now implemented via the derivation-producing function.
buildDerivation :: Typ -> Typ -> Bool -> InferMonad [Derivation]
buildDerivation source target _ = do
  (_, d) <- nominalSubDeriv source target
  return [d]

-- Clean interface function (string inputs)
runNominalSubtypingAlg :: String -> String -> String
runNominalSubtypingAlg leftTypeStr rightTypeStr = 
  case (parseTyp leftTypeStr, parseTyp rightTypeStr) of
    (Left err, _) -> toJson $ InferResult False Nothing [] (Just $ "Source type parse error: " ++ err) False
    (_, Left err) -> toJson $ InferResult False Nothing [] (Just $ "Target type parse error: " ++ err) False
    (Right source, Right target) -> toJson $ runNominalSubtyping source target
