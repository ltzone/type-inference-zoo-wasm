{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Subtyping.Recursive.Distributive where


import Lib (Derivation (..), InferMonad, InferResult (..), freshTVar, runInferMonad)
import Syntax (Typ (..), LabelVar)
import Unbound.Generics.LocallyNameless (subst, unbind, swaps)
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Unbound.Generics.LocallyNameless.Name (AnyName (..))
import Unbound.Generics.LocallyNameless.Operations (bind)
import Control.Monad.Except (throwError)
import Data.Map.Strict (singleton)
import Unbound.Generics.PermM (single)



-- controlled splitting
-- flag: true for cspl and False for sspl
ruleSplName :: Bool -> String -> String
ruleSplName True s = "CSpl-" ++ s
ruleSplName False s = "SSpl-" ++ s

ruleOrdName :: Bool -> String -> String
ruleOrdName True s = "COrd-" ++ s
ruleOrdName False s = "SOrd-" ++ s

ruleSplExpression :: Bool -> Typ -> Typ -> Typ -> String
ruleSplExpression True a a1 a2 =
  show a1 ++ "~\\lhd~" ++ show a ++ "~\\rhd~" ++ show a2
ruleSplExpression False a a1 a2 =
  show a1 ++ "~\\blacktriangleleft~" ++ show a ++ "~\\blacktriangleright~" ++ show a2

ruleOrdExpression :: Bool -> Typ -> String
ruleOrdExpression True a = show a ++ " ^{\\circ}"
ruleOrdExpression False a = show a ++ " ^{\\bullet}"


freeLabelNeg :: Bool -> Typ -> InferMonad [LabelVar]
freeLabelNeg p t = case t of
  TTop -> return []
  TBot -> return []
  TInt -> return []
  TBool -> return []
  TVar _ -> return []
  ETVar _ -> return []
  STVar _ -> return []
  TArr a b -> do
    as <- freeLabelNeg (not p) a
    bs <- freeLabelNeg p b
    return (as ++ bs)
  TAllB _ _ -> throwError $ "forall not supported"
  TIntersection a b -> do
    as <- freeLabelNeg p a
    bs <- freeLabelNeg p b
    return (as ++ bs)
  TUnion a b -> do
    as <- freeLabelNeg p a
    bs <- freeLabelNeg p b
    return (as ++ bs)
  TTuple ts -> do
    tss <- mapM (freeLabelNeg p) ts
    return (concat tss)
  TRecursive _ -> throwError $ "free labels should not be computed for source types"
  TLabel _ a -> freeLabelNeg p a
  TLabeled l bnd -> do
    (x, a) <- unbind bnd
    as <- freeLabelNeg p a
    return $ filter (/= x) as ++ ([l | not p])
    -- maybe we don't even need to drop x since x is a bound variable not label
  TTranslatedMu bnd -> do
    ((a, l), body) <- unbind bnd
    bs <- freeLabelNeg p body
    return $ filter (/= l) $ filter (/= a) bs ++ ([l | not p])



cspl :: Bool -> Typ -> InferMonad (Maybe (Typ, Typ) , Derivation)
cspl flag (TIntersection a b) =
  return (Just (a, b), Derivation {
    ruleId = ruleSplName flag "and",
    expression = ruleSplExpression flag (TIntersection a b) a b,
    children = []
  })
cspl flag (TArr a b) = do
  (bSpl, drv) <- cspl flag b
  case bSpl of
    Just (b1, b2) ->
      let a1 = TArr a b1
          a2 = TArr a b2 in
      return (Just (a1, a2), Derivation {
        ruleId = ruleSplName flag "arr",
        expression = ruleSplExpression flag (TArr a b) a1 a2,
        children = [drv]
      })
    Nothing -> return (Nothing, Derivation {
      ruleId = ruleOrdName flag "arr",
      expression = ruleOrdExpression flag (TArr a b),
      children = [drv]
    })
cspl flag (TLabel l a) = do
  (aSpl, drv) <- cspl flag a
  case aSpl of
    Just (a1, a2) ->
      let t1 = TLabel l a1
          t2 = TLabel l a2 in
      return (Just (t1, t2), Derivation {
        ruleId = ruleSplName flag "rcd",
        expression = ruleSplExpression flag (TLabel l a) t1 t2,
        children = [drv]
      })
    Nothing -> return (Nothing, Derivation {
      ruleId = ruleOrdName flag "rcd",
      expression = ruleOrdExpression flag (TLabel l a),
      children = [drv]
    })
-- simple splitting:
cspl False (TTranslatedMu bnd) = do
  ((a, l), body) <- unbind bnd
  isNegBody <- elem l <$> freeLabelNeg True body
  (bodySpl, drv) <- cspl False body
  case (bodySpl, isNegBody) of
    (Just (b1, b2), False) ->
      let t1 = TTranslatedMu (bind (a, l) b1)
          t2 = TTranslatedMu (bind (a, l) b2) in
      return (Just (t1, t2), Derivation {
        ruleId = ruleSplName False "mu",
        expression = ruleSplExpression False (TTranslatedMu bnd) t1 t2,
        children = [drv]
      })
    (_, _) -> return (Nothing, Derivation {
      ruleId = ruleOrdName False "mu",
      expression = ruleOrdExpression False (TTranslatedMu bnd),
      children = [drv]
    })
-- controlled splitting:
cspl True (TTranslatedMu bnd) = do
  ((a, l), body) <- unbind bnd
  isNegBody <- elem l <$> freeLabelNeg True body
  (bodySpl, drv) <- cspl (not isNegBody) body
  -- if negative, then simple splitting
  -- otherwise, controlled splitting
  case bodySpl of
    Just (b1, b2) ->
      let t1 = TTranslatedMu (bind (a, l) b1)
          t2 = TTranslatedMu (bind (a, l) b2) in
      return (Just (t1, t2), Derivation {
        ruleId = ruleSplName True "mu",
        expression = ruleSplExpression True (TTranslatedMu bnd) t1 t2,
        children = [drv]
      })
    Nothing -> return (Nothing, Derivation {
      ruleId = ruleOrdName True "mu",
      expression = ruleOrdExpression True (TTranslatedMu bnd),
      children = [drv]
    })
cspl flag t = return (Nothing, Derivation {
  ruleId = ruleOrdName flag "base",
  expression = ruleOrdExpression flag t,
  children = []
})



toplike :: Typ -> Bool
toplike TTop = True
toplike (TArr _ b) = toplike b
toplike (TIntersection a b) = toplike a && toplike b
toplike (TLabel _ a) = toplike a
toplike (TTranslatedMu bnd) =
  let (_, body) = unsafeUnbind bnd in
  toplike body
toplike _ = False


bcdSubDeriv :: Typ -> Typ -> InferMonad (Bool, Derivation)
bcdSubDeriv leftTyp rightTyp = do
  (rightTypSpl, drv) <- cspl True rightTyp
  case rightTypSpl of
    Just (r1, r2) -> do
      (res1, drv1) <- bcdSubDeriv leftTyp r1
      (res2, drv2) <- bcdSubDeriv leftTyp r2
      let ok = res1 && res2
      return (ok, Derivation {
        ruleId = "S-and",
        expression = show leftTyp ++ " <: " ++ show rightTyp,
        children = [drv, drv1, drv2]
      })
    Nothing -> bcdSubDerivAux leftTyp rightTyp where
      bcdSubDerivAux :: Typ -> Typ -> InferMonad (Bool, Derivation)
      bcdSubDerivAux _ rty | toplike rty = do
        return (True, Derivation {
          ruleId = "S-top",
          expression = show leftTyp ++ " <: " ++ show rty,
          children = [ Derivation {
            ruleId = "Top-like",
            expression = "\\lceil" ++ show rty ++ " \\ rceil",
            children = []
          } ]
        })
      bcdSubDerivAux TInt TInt = return (True, Derivation {
        ruleId = "S-int",
        expression = "\\texttt{Int} <: \\texttt{Int}",
        children = []
      })
      bcdSubDerivAux TBool TBool = return (True, Derivation {
        ruleId = "S-bool",
        expression = "\\texttt{Bool} <: \\texttt{Bool}",
        children = []
      })
      bcdSubDerivAux (TVar v1) (TVar v2) =
        let ok = v1 == v2 in
        return (ok, Derivation {
          ruleId = "S-var",
          expression = show (TVar v1) ++ " <: " ++ show (TVar v2),
          children = []
        })
      bcdSubDerivAux (TArr s1 s2) (TArr t1 t2) = do
        (r1, d1) <- bcdSubDeriv t1 s1
        (r2, d2) <- bcdSubDeriv s2 t2
        let ok = r1 && r2
        return (ok, Derivation {
          ruleId = "S-arrow",
          expression = show (TArr s1 s2) ++ " <: " ++ show (TArr t1 t2),
          children = [d1, d2]
        })
      bcdSubDerivAux (TIntersection s1 s2) t = do
        (r1, d1) <- bcdSubDeriv s1 t
        (r2, d2) <- bcdSubDeriv s2 t
        if r1 then return (
          True, Derivation {
            ruleId = "S-andl",
            expression = show (TIntersection s1 s2) ++ " <: " ++ show t,
            children = [d1]
          }
          ) else if r2 then return (
          True, Derivation {
            ruleId = "S-andr",
            expression = show (TIntersection s1 s2) ++ " <: " ++ show t,
            children = [d2]
          }
          ) else return (
          False, Derivation {
            ruleId = "S-and",
            expression = show (TIntersection s1 s2) ++ " <: " ++ show t,
            children = [d1, d2]
          }
          ) 
      bcdSubDerivAux (TLabel l1 a) (TLabel l2 b) =
        if l1 == l2 then do
          (r, d) <- bcdSubDeriv a b
          return (r, Derivation {
            ruleId = "S-label",
            expression = show (TLabel l1 a) ++ " <: " ++ show (TLabel l2 b),
            children = [d]
          })
        else return (False, Derivation {
          ruleId = "S-fail",
          expression = "label mismatch: " ++ show l1 ++ " vs. " ++ show l2,
          children = []
        })
      bcdSubDerivAux (TLabeled l1 bnd1) (TLabeled l2 bnd2) = do
        if l1 == l2 then do
          (x1, a) <- unbind bnd1
          (x2, b) <- unbind bnd2
          let b' = subst x2 (TVar x1) b
          (r, d) <- bcdSubDeriv a b'
          return (r, Derivation {
            ruleId = "S-labeled",
            expression = show (TLabeled l1 bnd1) ++ " <: " ++ show (TLabeled l2 bnd2),
            children = [d]
          })
        else return (False, Derivation {
          ruleId = "S-fail",
          expression = "label mismatch: " ++ show l1 ++ " vs. " ++ show l2,
          children = []
        })
      bcdSubDerivAux a (TTranslatedMu bndB) = do
        ((xB, lB), bodyB) <- unbind bndB
        (bodySpl, drvB) <- cspl False bodyB
        case bodySpl of
          -- The right type body is ordinary, apply the conventional S-rec rule
          Nothing -> case a of
            TTranslatedMu bndA -> do
              ((xA, lA), bodyA) <- unbind bndA
              let bodyA' = subst xA (TVar xB) (swaps (single (AnyName lA) (AnyName lB)) bodyA)
              (ok, d) <- bcdSubDeriv bodyA' bodyB
              return (ok, Derivation {
                ruleId = "S-rec",
                expression = show (TTranslatedMu bndA) ++ " <: " ++ show (TTranslatedMu bndB),
                children = [drvB, d]
              })
            _ -> return (False, Derivation {
              ruleId = "S-fail",
              expression = "left type is not recursive: " ++ show a,
              children = [drvB]
            })
          Just _ -> return (False, Derivation {
            ruleId = "S-fail",
            expression = "[TODO] right type is distributive: " ++ show (TTranslatedMu bndB),
            children = [drvB]
          })
      bcdSubDerivAux _ _ = return (False, Derivation {
        ruleId = "S-fail",
        expression = "no applicable rule for: " ++ show leftTyp ++ " <: " ++ show rightTyp,
        children = []
      })


        

