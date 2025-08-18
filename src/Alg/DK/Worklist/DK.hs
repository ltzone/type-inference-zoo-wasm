{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

module Alg.DK.Worklist.DK (runWorklist) where

import Alg.DK.Common (isAll)
import Alg.DK.Worklist.Common (Entry (..), Judgment (..), TBind (..), Worklist, before, initWL, runInfer, substWL)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Data.Foldable (find)
import Lib (Derivation (..), InferMonad, InferResult (..), freshTVar)
import Syntax (Trm (..), Typ (..), latexifyVar, pattern TAll)
import Unbound.Generics.LocallyNameless
  ( Fresh (fresh),
    Subst (subst),
    bind,
    fv,
    substBind,
    unbind,
  )
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

infer :: String -> Worklist -> InferMonad [Derivation]
infer rule ws = do
  lift $ tell [show ws]
  case ws of
    [] -> ret rule []
    WTVar _ _ : ws' -> do
      drvs <- infer "GCTVar" ws'
      ret "GCTVar" drvs
    WVar _ _ : ws' -> do
      drvs <- infer "GCVar" ws'
      ret "GCVar" drvs
    WJug (Sub TInt TInt) : ws' -> do
      drvs <- infer "SubReflInt" ws'
      ret "SubReflInt" drvs
    WJug (Sub TBool TBool) : ws' -> do
      drvs <- infer "SubReflBool" ws'
      ret "SubReflBool" drvs
    WJug (Sub (TVar a) (TVar b)) : ws' | a == b -> do
      drvs <- infer "SubReflTVar" ws'
      ret "SubReflTVar" drvs
    WJug (Sub (ETVar a) (ETVar b)) : ws' | a == b -> do
      drvs <- infer "SubReflETVar" ws'
      ret "SubReflETVar" drvs
    WJug (Sub (TArr ty1 ty2) (TArr ty1' ty2')) : ws' -> do
      let ws'' = WJug (Sub ty1' ty1) : WJug (Sub ty2 ty2') : ws'
      drvs <- infer "SubArr" ws''
      ret "SubArr" drvs
    WJug (Sub (TAll bnd) ty2) : ws' | not (isAll ty2) -> do
      (a, ty1) <- unbind bnd
      let ty1' = subst a (ETVar a) ty1
          ws'' = WJug (Sub ty1' ty2) : WTVar a ETVarBind : ws'
      drvs <- infer "SubAllL" ws''
      ret "SubAllL" drvs
    WJug (Sub ty1 (TAll bnd)) : ws' -> do
      (a, ty2) <- unbind bnd
      let ws'' = WJug (Sub ty1 ty2) : WTVar a TVarBind : ws'
      drvs <- infer "SubAllR" ws''
      ret "SubAllR" drvs
    WJug (Sub (ETVar a) ty@(TArr ty1 ty2)) : ws'
      | a `notElem` toListOf fv ty -> do
          a1 <- fresh a
          a2 <- fresh a
          ws'' <- substWL a (TArr (ETVar a1) (ETVar a2)) [WTVar a1 ETVarBind, WTVar a2 ETVarBind] ws'
          let ws''' = WJug (Sub (TArr (ETVar a1) (ETVar a2)) (TArr ty1 ty2)) : ws''
          drvs <- infer "SubSplitL" ws'''
          ret "SubSplitL" drvs
    WJug (Sub ty@(TArr ty1 ty2) (ETVar a)) : ws'
      | a `notElem` toListOf fv ty -> do
          a1 <- fresh a
          a2 <- fresh a
          ws'' <- substWL a (TArr (ETVar a1) (ETVar a2)) [WTVar a1 ETVarBind, WTVar a2 ETVarBind] ws'
          let ws''' = WJug (Sub (TArr ty1 ty2) (TArr (ETVar a1) (ETVar a2))) : ws''
          drvs <- infer "SubSplitR" ws'''
          ret "SubSplitR" drvs
    WJug (Sub (ETVar a) (ETVar b)) : ws' | before ws' a b -> do
      ws'' <- substWL b (ETVar a) [] ws'
      drvs <- infer "SubInstETVar1" ws''
      ret "SubInstETVar1" drvs
    WJug (Sub (ETVar b) (ETVar a)) : ws' | before ws' a b -> do
      ws'' <- substWL b (ETVar a) [] ws'
      drvs <- infer "SubInstETVar2" ws''
      ret "SubInstETVar2" drvs
    WJug (Sub (TVar a) (ETVar b)) : ws' | before ws' a b -> do
      ws'' <- substWL b (TVar a) [] ws'
      drvs <- infer "SubInstETVar3" ws''
      ret "SubInstETVar3" drvs
    WJug (Sub (ETVar b) (TVar a)) : ws' | before ws' a b -> do
      ws'' <- substWL b (ETVar a) [] ws'
      drvs <- infer "SubInstETVar4" ws''
      ret "SubInstETVar4" drvs
    WJug (Sub TInt (ETVar b)) : ws' -> do
      ws'' <- substWL b TInt [] ws'
      drvs <- infer "SubInstETVar5" ws''
      ret "SubInstETVar5" drvs
    WJug (Sub (ETVar b) TInt) : ws' -> do
      ws'' <- substWL b TInt [] ws'
      drvs <- infer "SubInstETVar6" ws''
      ret "SubInstETVar6" drvs
    WJug (Sub TBool (ETVar b)) : ws' -> do
      ws'' <- substWL b TBool [] ws'
      drvs <- infer "SubInstETVar7" ws''
      ret "SubInstETVar7" drvs
    WJug (Sub (ETVar b) TBool) : ws' -> do
      ws'' <- substWL b TBool [] ws'
      drvs <- infer "SubInstETVar8" ws''
      ret "SubInstETVar8" drvs
    WJug End : ws' -> do
      drvs <- infer "End" ws'
      ret "End" drvs
    WJug (Chk tm (TAll bnd)) : ws' -> do
      (a, ty) <- unbind bnd
      let ws'' = WJug (Chk tm ty) : WTVar a TVarBind : ws'
      drvs <- infer "ChkAll" ws''
      ret "ChkAll" drvs
    WJug (Chk (Lam bnd) (TArr ty1 ty2)) : ws' -> do
      (x, e) <- unbind bnd
      let ws'' = WJug (Chk e ty2) : WVar x ty1 : ws'
      drvs <- infer "ChkLam" ws''
      ret "ChkLam" drvs
    WJug (Chk (Lam bnd) (ETVar a)) : ws' -> do
      (x, e) <- unbind bnd
      a1 <- fresh a
      a2 <- fresh a
      ws'' <-
        substWL a (TArr (ETVar a1) (ETVar a2)) [WTVar a1 ETVarBind, WTVar a2 ETVarBind] $
          WJug (Chk e (ETVar a2)) : WVar x (ETVar a1) : ws'
      drvs <- infer "ChkLamSplit" ws''
      ret "ChkLamSplit" drvs
    WJug (Chk tm ty) : ws' -> do
      a <- freshTVar
      let ws'' = WJug (Inf tm (bind a (Sub (TVar a) ty))) : ws'
      drvs <- infer "ChkSub" ws''
      ret "ChkSub" drvs
    WJug (Inf (Var x) j) : ws' -> do
      case find (\case WVar x' _ -> x == x'; _ -> False) ws' of
        Just (WVar _ ty) -> do
          let ws'' = WJug (substBind j ty) : ws'
          drvs <- infer "InfVar" ws''
          ret "InfVar" drvs
        _ -> throwError $ "\\text{Variable } " ++ latexifyVar x ++ " \\text{ is not found}"
    WJug (Inf (Ann tm ty) j) : ws' -> do
      let ws'' = WJug (Chk tm ty) : WJug (substBind j ty) : ws'
      drvs <- infer "InfAnn" ws''
      ret "InfAnn" drvs
    WJug (Inf (LitInt _) j) : ws' -> do
      let ws'' = WJug (substBind j TInt) : ws'
      drvs <- infer "InfLitInt" ws''
      ret "InfLitInt" drvs
    WJug (Inf (LitBool _) j) : ws' -> do
      let ws'' = WJug (substBind j TBool) : ws'
      drvs <- infer "InfLitBool" ws''
      ret "InfLitBool" drvs
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
      drvs <- infer "InfLam" ws''
      ret "InfLam" drvs
    WJug (Inf (App tm1 tm2) j) : ws' -> do
      a <- freshTVar
      let ws'' = WJug (Inf tm1 (bind a (InfApp (TVar a) tm2 j))) : ws'
      drvs <- infer "InfApp" ws''
      ret "InfApp" drvs
    WJug (InfApp (TAll bnd) tm j) : ws' -> do
      (a, ty) <- unbind bnd
      let ws'' = WJug (InfApp (subst a (ETVar a) ty) tm j) : WTVar a ETVarBind : ws'
      drvs <- infer "InfAppAll" ws''
      ret "InfAppAll" drvs
    WJug (InfApp (TArr ty1 ty2) tm j) : ws' -> do
      let ws'' = WJug (Chk tm ty1) : WJug (substBind j ty2) : ws'
      drvs <- infer "InfAppArr" ws''
      ret "InfAppArr" drvs
    WJug (InfApp (ETVar a) tm j) : ws' -> do
      a1 <- fresh a
      a2 <- fresh a
      ws'' <-
        substWL a (TArr (ETVar a1) (ETVar a2)) [WTVar a1 ETVarBind, WTVar a2 ETVarBind] $
          WJug (InfApp (TArr (ETVar a1) (ETVar a2)) tm j) : ws'
      drvs <- infer "InfAppETVar" ws''
      ret "InfAppETVar" drvs
    _ -> throwError $ "\\text{No matching rule for } " ++ show ws
  where
    ret :: String -> [Derivation] -> InferMonad [Derivation]
    ret ruleName drvs = do
      lift $ tell ["\\text{" ++ ruleName ++ ": } " ++ show ws]
      return $ (Derivation ruleName (show ws) []) : drvs

runWorklist :: Trm -> InferResult
runWorklist tm = runInfer infer (initWL tm)
