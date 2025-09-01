{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Subtyping.Recursive.Distributive (distributiveMeta, runDistributiveSubtyping) where


import Lib (Derivation (..), InferMonad, InferResult (..), freshTVar, runInferMonad, AlgMeta(..), Paper (..), Example (..))
import Syntax (Typ (..), LabelVar, TyVar)
import Unbound.Generics.LocallyNameless (subst, unbind, swaps)
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Unbound.Generics.LocallyNameless.Name (AnyName (..))
import Unbound.Generics.LocallyNameless.Operations (bind)
import Control.Monad.Except (throwError)
import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Unbound.Generics.PermM (single)
import Subtyping.Recursive.Lib (SubtypingResult(..))
import Subtyping.Recursive.Translate (translation)
import Control.Monad.ST (ST)
import Data.List (subsequences)
import Unbound.Generics.LocallyNameless (s2n)



distributiveMeta :: AlgMeta
distributiveMeta = AlgMeta
  { metaId = "Distributive"
  , metaName = "Distributive Subtyping by translation"
  , metaLabels = ["Subtyping", "System Fsub", "Recursive Types"]
  , metaViewMode = "tree"
  , metaMode = "subtyping"
  , metaPaper = Paper
    { paperTitle = "Distributive Subtyping"
    , paperAuthors = ["Litao Zhou"]
    , paperYear = 2025
    , paperUrl = "TBD"
    }
  , metaVariants = Nothing
  , metaDefaultVariant = Nothing
  , metaRules = []
  , metaRuleGroups = Nothing
  , metaVariantRules = Nothing
  , metaExamples = 
    [ Example
      { exampleName = "The tricky case 1"
      , exampleExpression = "(mu a. Top -> (mu b. Top -> Int)) & (mu a. Top -> (mu b. b -> Bool)) <: (mu a. a -> (mu b. (b -> Int) & (b -> Bool)))"
      , exampleDescription = "The right type is ordinary but the body is splittable, the corner case is reached"
      }
    , Example
      { exampleName = "The tricky case 2"
      , exampleExpression = "(mu a. (mu b. b -> Int)) & (mu a. (mu b. a -> Bool)) <: (mu a. (mu b. (b -> Int) & (a -> Bool)))"
      , exampleDescription = "This is not derivable in the source declarative rules"
      }
    , Example
      { exampleName = "The tricky case 2 -- related"
      , exampleExpression = "(mu a. (mu b. b -> Int)) & (mu a. (mu b. a -> Bool)) <: (mu a. ((mu b. (b -> Int)) & (mu b. (a -> Bool))))"
      , exampleDescription = "One layer merge, however, should be allowed."
      }
    , Example
      { exampleName = "Positive Recursive Types"
      , exampleExpression = "mu a. Top -> a <: mu a. Int -> a"
      , exampleDescription = "Positive recursive subtyping"
      }
    , Example
      { exampleName = "Negative Recursive Types (Fail)"
      , exampleExpression = "mu a. a -> Int <: mu a. a -> Bool"
      , exampleDescription = "Negative recursive subtyping"
      }
    , Example
      { exampleName = "Negative Recursive Types + Top"
      , exampleExpression = "mu a. Top -> Int <: mu a. a -> Int"
      , exampleDescription = "Recursive type subtyping"
      }
    , Example
      { exampleName = "Nested Recursive Subtyping"
      , exampleExpression = "mu a. Top -> (mu b. b -> a) <: mu a. Int -> (mu b. b -> a)"
      , exampleDescription = "Nested recursive subtyping"
      }
    ]
  }



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
    return $ filter (/= l) $ filter (/= a) bs



-- controlled splitting
-- flag: true for cspl and False for sspl
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
      tryIntersectionDeriv :: Typ -> Typ -> Typ -> InferMonad (Bool, Derivation)
      tryIntersectionDeriv s1 s2 t = do
        (r1, d1) <- bcdSubDeriv s1 t
        (r2, d2) <- bcdSubDeriv s2 t
        if r1 then return
          (True, Derivation {
            ruleId = "S-andl",
            expression = show (TIntersection s1 s2) ++ " <: " ++ show t,
            children = [d1]
          })
        else if r2 then return
          (True, Derivation {
            ruleId = "S-andr",
            expression = show (TIntersection s1 s2) ++ " <: " ++ show t,
            children = [d2]
          })
        else return
          (False, Derivation {
            ruleId = "S-and",
            expression = show (TIntersection s1 s2) ++ "\\textcolor{red}{\\nleq}" ++ show t,
            children = [d1, d2]
          })

      bcdSubDerivAux :: Typ -> Typ -> InferMonad (Bool, Derivation)
      bcdSubDerivAux _ rty | toplike rty = do
        return (True, Derivation {
          ruleId = "S-top",
          expression = show leftTyp ++ " <: " ++ show rty,
          children = [ Derivation {
            ruleId = "Top-like",
            expression = "\\lceil" ++ show rty ++ " \\rceil",
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
        (bodySpl, drvB) <- cspl True bodyB
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
            -- fall back to intersection rules
            TIntersection s1 s2 -> do
              (interOk, drvInter) <- tryIntersectionDeriv s1 s2 (TTranslatedMu bndB)
              return (interOk, Derivation {
                ruleId = "S-intersection",
                expression = show (TIntersection s1 s2) ++ " <: " ++ show (TTranslatedMu bndB),
                children = [drvB, drvInter]
              })
            _ -> return (False, Derivation {
              ruleId = "S-fail",
              expression = "left type is not recursive: " ++ show a,
              children = [drvB]
            })

          -- The right type body is splittble, while the recursive type is still ordinary
          -- try the generalized rules:
          Just _ -> do
            -- open the left type with the same right type variable
            aOpenLis <- mcodPos xB lB a
            let aOpenCombs = allMcod aOpenLis
            results <- mapM (\aOpen -> do
                isNegA <- elem lB <$> freeLabelNeg True aOpen
                if isNegA then do
                  -- isomorphic test
                  aOpen' <- dropLabel lB aOpen
                  bodyB' <- dropLabel lB bodyB
                  (r1, d1) <- bcdSubDeriv aOpen' bodyB'
                  (r2, d2) <- bcdSubDeriv bodyB' aOpen'
                  let ok = r1 && r2
                  return (ok, Derivation {
                    ruleId = "S-mu-neg",
                    expression = show a ++ " <: " ++ show (TTranslatedMu bndB),
                    children = [Derivation {
                      ruleId = "S-mu-neg-iso",
                      expression = show aOpen ++ " ~\\equiv~ " ++ show bodyB,
                      children = [d1, d2]
                    }]
                  })
                else do
                  -- subtyping test
                    (ok, d) <- bcdSubDeriv aOpen bodyB
                    return (ok, Derivation {
                      ruleId = "S-mu-pos",
                      expression = show a ++ " <: " ++ show (TTranslatedMu bndB),
                      children = [Derivation {
                       ruleId = "S-mu-pos-sub",
                       expression = show aOpen ++ " <: " ++ show bodyB,
                       children = [d]
                      }
                      ]
                    })
              ) aOpenCombs
            let firstOk = foldr (\(ok, d) acc -> if ok then Just (ok, d) else acc) Nothing results
            case firstOk of
              Just (ok, d) -> return (ok, d)
              Nothing -> return (False, Derivation {
                ruleId = "S-mu-fail",
                expression = show a ++ " \\nleq " ++ show (TTranslatedMu bndB),
                children = map snd results
                })
      bcdSubDerivAux (TIntersection s1 s2) t = tryIntersectionDeriv s1 s2 t
      bcdSubDerivAux _ _ = return (False, Derivation {
        ruleId = "S-fail",
        expression = "no applicable rule for: " ++ show leftTyp ++ " <: " ++ show rightTyp,
        children = []
      })


parts :: Typ -> [Typ]
parts (TIntersection a b) = parts a ++ parts b
parts (TArr a b) = [TArr a b' | b' <- parts b]
parts (TLabel l a) = [TLabel l a' | a' <- parts a]
parts t = [t]


mcodPos :: TyVar -> LabelVar -> Typ -> InferMonad [Typ]
mcodPos x l (TIntersection a b) = do
  as <- mcodPos x l a
  bs <- mcodPos x l b
  return (as ++ bs)
mcodPos x l (TTranslatedMu bnd) = do
  ((y, l'), body) <- unbind bnd
  isBodyNeg <- elem l' <$> freeLabelNeg True body
  if isBodyNeg then
    return [subst y (TVar x) (swaps (single (AnyName l') (AnyName l)) body)]
  else
    return $ parts $ subst y (TVar x) (swaps (single (AnyName l') (AnyName l)) body)
mcodPos _ _ _ = return []


foldSAnd :: [Typ] -> Typ
foldSAnd [] = TTop
foldSAnd [t] = t
foldSAnd (t : ts) = TIntersection t (foldSAnd ts)



allMcod :: [Typ] -> [Typ]
allMcod types = map foldSAnd (subsequences types)



dropLabel :: LabelVar -> Typ -> InferMonad Typ
dropLabel l TTop = return TTop
dropLabel l TBot = return TBot
dropLabel l TInt = return TInt
dropLabel l TBool = return TBool
dropLabel l (TVar v) = return $ TVar v
dropLabel l (ETVar v) = return $ ETVar v
dropLabel l (STVar v) = return $ STVar v
dropLabel l (TArr a b) = do 
  a' <- dropLabel l a
  b' <- dropLabel l b
  return $ TArr a' b'
dropLabel l (TAllB v t) = do
  (x, bnd) <- unbind v
  v' <- dropLabel l bnd
  t' <- dropLabel l t
  return $ TAllB (bind x v') t'
dropLabel l (TIntersection a b) = do
  a' <- dropLabel l a
  b' <- dropLabel l b
  return $ TIntersection a' b'
dropLabel l (TUnion a b) = do
  a' <- dropLabel l a
  b' <- dropLabel l b
  return $ TUnion a' b'
dropLabel l (TTuple ts) = do
  ts' <- mapM (dropLabel l) ts
  return $ TTuple ts'
dropLabel l (TRecursive b) = do
  (x, bnd) <- unbind b
  bnd' <- dropLabel l bnd
  return $ TRecursive (bind x bnd')
dropLabel l (TLabel l' a) | l == l' = return $ TLabel l' TBool
                          | otherwise = do
    a' <- dropLabel l a
    return $ TLabel l' a'
dropLabel l (TLabeled l' bnd) | l == l' = return $ TLabeled l' (bind (s2n "x") TBool)
                              | otherwise = do
    (x, a) <- unbind bnd
    a' <- dropLabel l a
    return $ TLabeled l' (bind x a')
dropLabel l (TTranslatedMu bnd) = do
  ((x, l'), body) <- unbind bnd
  body' <- dropLabel l body
  return $ TTranslatedMu (bind (x, l') body')




runDistributiveSubtyping :: Typ -> Typ -> InferResult
runDistributiveSubtyping s t =case runInferMonad $ do
  lift $ tell ["\\textbf{Distributive Subtyping: }" ++ show s ++ " <: " ++ show t]
  (srcTrans, d1) <- translation s
  lift $ tell ["\\textbf{Source type translated to: }" ++ show srcTrans]
  (tgtTrans, d2) <- translation t
  lift $ tell ["\\textbf{Target type translated to: }" ++ show tgtTrans]
  (ok, d3) <- bcdSubDeriv srcTrans tgtTrans
  return $ SubtypingResult
    { isSubtype = ok
    , leftType = srcTrans
    , rightType = tgtTrans
    , subtypingDerivation = [ d3, d1, d2]
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