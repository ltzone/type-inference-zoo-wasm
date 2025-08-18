{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

-- TODO: This is a simplified version of the IU algorithm
-- The full version with logic programming and backtracking would be more complex

module Alg.DK.Worklist.IU (runIU) where

import Alg.DK.Worklist.Common (Entry (..), Judgment (..), TBind (..), Worklist, initWL, runInfer, substWLOrd)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Data.Foldable (find)
import Lib (Derivation (..), InferMonad, InferResult (..), freshTVar)
import Syntax (Trm (..), Typ (..), latexifyVar, pattern TAll, pattern TLam)
import Unbound.Generics.LocallyNameless
  ( Fresh (fresh),
    Subst (subst),
    bind,
    fv,
    substBind,
    unbind,
  )
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

notAll :: Typ -> Bool
-- TODO: we should be careful about the wildcard when extending more types
notAll TInt = True
notAll TBool = True
notAll TTop = True
notAll TBot = False
notAll (TArr _ _) = True
notAll (TVar _) = True
notAll (ETVar _) = True
notAll (STVar _) = False
notAll (TAll _) = False
notAll (TIntersection ty1 ty2) = notAll ty1 && notAll ty2
notAll (TUnion ty1 ty2) = notAll ty1 || notAll ty2
notAll _ = False

mono :: Typ -> Bool
mono TInt = True
mono TBool = True
mono TTop = False
mono TBot = False
mono (TArr ty1 ty2) = mono ty1 && mono ty2
mono (TVar _) = True
mono (ETVar _) = True
mono (STVar _) = False
mono (TAll _) = False
mono (TIntersection _ _) = False
mono (TUnion _ _) = False
mono _ = False

infer :: String -> Worklist -> InferMonad Derivation
infer rule ws = do
  lift $ tell ["\\text{" ++ rule ++ ": } " ++ show ws]
  case ws of
    [] -> ret rule "\\text{Empty worklist}" []
    WTVar _ _ : ws' -> do
      drv <- infer "GCTVar" ws'
      ret rule "\\text{Garbage collect type variable}" [drv]
    WVar _ _ : ws' -> do
      drv <- infer "GCVar" ws'
      ret rule "\\text{Garbage collect variable}" [drv]
    WJug (Sub TInt TInt) : ws' -> do
      drv <- infer "SubReflInt" ws'
      ret rule (show ws ++ " \\leadsto " ++ show ws') [drv]
    WJug (Sub TBool TBool) : ws' -> do
      drv <- infer "SubReflBool" ws'
      ret rule (show ws ++ " \\leadsto " ++ show ws') [drv]
    WJug (Sub (TVar a) (TVar b)) : ws' | a == b -> do
      drv <- infer "SubReflTVar" ws'
      ret rule (show ws ++ " \\leadsto " ++ show ws') [drv]
    WJug (Sub (ETVar a) (ETVar b)) : ws' | a == b -> do
      drv <- infer "SubReflETVar" ws'
      ret rule (show ws ++ " \\leadsto " ++ show ws') [drv]
    WJug (Sub (STVar a) (STVar b)) : ws' | a == b -> do
      drv <- infer "SubReflSTVar" ws'
      ret rule (show ws ++ " \\leadsto " ++ show ws') [drv]
    WJug (Sub _ TTop) : ws' -> do
      drv <- infer "SubTop" ws'
      ret rule (show ws ++ " \\leadsto " ++ show ws') [drv]
    WJug (Sub TBot _) : ws' -> do
      drv <- infer "SubBot" ws'
      ret rule (show ws ++ " \\leadsto " ++ show ws') [drv]
    WJug (Sub (TArr ty1 ty2) (TArr ty1' ty2')) : ws' -> do
      let ws'' = WJug (Sub ty1' ty1) : WJug (Sub ty2 ty2') : ws'
      drv <- infer "SubArr" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (TAll bnd1) (TAll bnd2)) : ws' -> do
      a <- freshTVar
      let ty1 = substBind bnd1 (ETVar a)
          ty2 = substBind bnd2 (ETVar a)
          ws'' = WJug (Sub ty1 ty2) : WTVar a STVarBind : ws'
      drv <- infer "SubAll" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (TAll bnd) ty2) : ws' | notAll ty2 -> do
      (a, ty1) <- unbind bnd
      let ty1' = subst a (ETVar a) ty1
          ws'' = WJug (Sub ty1' ty2) : WTVar a ETVarBind : ws'
      drv <- infer "SubAllL" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (ETVar a) ty) : ws'
      | a `notElem` toListOf fv ty,
        mono ty -> do
          ws'' <- substWLOrd a ty ws'
          drv <- infer "SubInstETVar" ws''
          ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub ty (ETVar a)) : ws'
      | a `notElem` toListOf fv ty,
        mono ty -> do
          ws'' <- substWLOrd a ty ws'
          drv <- infer "SubInstETVar" ws''
          ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    -- Simplified intersection/union handling
    WJug (Sub (TIntersection ty1 _) ty) : ws' -> do
      let ws'' = WJug (Sub ty1 ty) : ws'
      drv <- infer "SubIntersectionL" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub ty (TIntersection ty1 ty2)) : ws' -> do
      let ws'' = WJug (Sub ty ty1) : WJug (Sub ty ty2) : ws'
      drv <- infer "SubIntersection" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (TUnion ty1 ty2) ty) : ws' -> do
      let ws'' = WJug (Sub ty1 ty) : WJug (Sub ty2 ty) : ws'
      drv <- infer "SubUnion" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub ty (TUnion ty1 _)) : ws' -> do
      let ws'' = WJug (Sub ty ty1) : ws'
      drv <- infer "SubUnionL" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug End : ws' -> do
      drv <- infer "End" ws'
      ret rule (show ws ++ " \\leadsto " ++ show ws') [drv]
    WJug (Chk (Lam bnd) TTop) : ws' -> do
      (x, e) <- unbind bnd
      let ws'' = WJug (Chk e TTop) : WVar x TBot : ws'
      drv <- infer "ChkLamTop" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Chk (Lam bnd) (TArr ty1 ty2)) : ws' -> do
      (x, e) <- unbind bnd
      let ws'' = WJug (Chk e ty2) : WVar x ty1 : ws'
      drv <- infer "ChkLam" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Chk tm (TIntersection ty1 ty2)) : ws' -> do
      let ws'' = WJug (Chk tm ty1) : WJug (Chk tm ty2) : ws'
      drv <- infer "ChkIntersection" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Chk tm ty) : ws' -> do
      a <- freshTVar
      let ws'' = WJug (Inf tm (bind a (Sub (TVar a) ty))) : ws'
      drv <- infer "ChkSub" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Inf (Var x) j) : ws' -> do
      case find (\case WVar x' _ -> x == x'; _ -> False) ws' of
        Just (WVar _ ty) -> do
          let ws'' = WJug (substBind j ty) : ws'
          drv <- infer "InfVar" ws''
          ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
        _ -> throwError $ "\\text{Variable } " ++ latexifyVar x ++ " \\text{ is not found}"
    WJug (Inf (Ann tm ty) j) : ws' -> do
      let ws'' = WJug (Chk tm ty) : WJug (substBind j ty) : ws'
      drv <- infer "InfAnn" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Inf (TLam bnd) j) : ws' -> do
      (a, tm) <- unbind bnd
      case tm of
        Ann tm' ty -> do
          let ws'' = WJug (Chk tm' ty)
                       : WTVar a TVarBind
                       : WJug (substBind j (TAll (bind a ty)))
                       : ws'
          drv <- infer "InfTLam" ws''
          ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
        _ -> throwError $ "\\text{Term } " ++ show tm ++ " \\text{ is not an annotated term}"
    WJug (Inf (LitInt _) j) : ws' -> do
      let ws'' = WJug (substBind j TInt) : ws'
      drv <- infer "InfLitInt" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Inf (LitBool _) j) : ws' -> do
      let ws'' = WJug (substBind j TBool) : ws'
      drv <- infer "InfLitBool" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Inf (Lam bnd) j) : ws' -> do
      a <- freshTVar
      b <- freshTVar
      (x, e) <- unbind bnd
      let ws'' = WJug (Chk e (ETVar b))
                   : WVar x (ETVar a)
                   : WJug (substBind j (TArr (ETVar a) (ETVar b)))
                   : WTVar a ETVarBind
                   : WTVar b ETVarBind
                   : ws'
      drv <- infer "InfLam" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Inf (App tm1 tm2) j) : ws' -> do
      a <- freshTVar
      b <- freshTVar
      let j' = Inf tm1 $ bind a $ Match (TVar a) $ bind b $ InfApp (TVar b) tm2 j
          ws'' = WJug j' : ws'
      drv <- infer "InfApp" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Match ty@(TArr _ _) j) : ws' -> do
      let ws'' = WJug (substBind j ty) : ws'
      drv <- infer "MatchArr" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Match TBot j) : ws' -> do
      let ws'' = WJug (substBind j (TArr TBot TBot)) : ws'
      drv <- infer "MatchBot" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Match (TAll bnd) j) : ws' -> do
      (a, ty) <- unbind bnd
      let j' = Match (subst a (ETVar a) ty) j
          ws'' = WJug j' : WTVar a ETVarBind : ws'
      drv <- infer "MatchAll" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (InfApp (TArr ty1 ty2) tm j) : ws' -> do
      let ws'' = WJug (Chk tm ty1) : WJug (substBind j ty2) : ws'
      drv <- infer "InfApp" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (InfTApp (TAll bnd) ty2 j) : ws' -> do
      let ws'' = WJug (substBind j (substBind bnd ty2)) : ws'
      drv <- infer "InfTAppAll" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (InfTApp TBot _ j) : ws' -> do
      let ws'' = WJug (substBind j TBot) : ws'
      drv <- infer "InfTAppBot" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    _ -> throwError $ "\\text{No matching rule for } " ++ show ws
  where
    ret :: String -> String -> [Derivation] -> InferMonad Derivation
    ret ruleName expr drvs = do
      lift $ tell ["\\text{" ++ ruleName ++ ": } " ++ expr]
      return (Derivation ruleName expr drvs)

runIU :: Trm -> InferResult
runIU tm = case runInfer infer (initWL tm) of
  InferResult success finalType _ errorMsg errorLatex -> InferResult success finalType [] errorMsg errorLatex
