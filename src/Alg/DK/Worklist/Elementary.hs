{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

module Alg.DK.Worklist.Elementary (runElementary) where

import Alg.DK.Common (isAll)
import Alg.DK.Worklist.Common (Entry (..), Judgment (..), TBind (..), Worklist, before, initWL, runInfer, substWL)
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
    WJug (Sub (TAll bnd) ty2) : ws' | not (isAll ty2) -> do
      -- ty2 is not Top as well
      (a, ty1) <- unbind bnd
      let ty1' = subst a (ETVar a) ty1
          ws'' = WJug (Sub ty1' ty2) : WTVar a ETVarBind : ws'
      drv <- infer "SubAllL" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (TAll bnd1) (TAll bnd2)) : ws' -> do
      a <- freshTVar
      let ty1 = substBind bnd1 (ETVar a)
          ty2 = substBind bnd2 (ETVar a)
          ws'' = WJug (Sub ty1 ty2) : WTVar a STVarBind : ws'
      drv <- infer "SubAll" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (ETVar a) ty@(TArr ty1 ty2)) : ws'
      | a `notElem` toListOf fv ty -> do
          a1 <- fresh a
          a2 <- fresh a
          ws'' <- substWL a (TArr (ETVar a1) (ETVar a2)) [WTVar a1 ETVarBind, WTVar a2 ETVarBind] ws'
          let ws''' = WJug (Sub (TArr (ETVar a1) (ETVar a2)) (TArr ty1 ty2)) : ws''
          drv <- infer "SubSplitL" ws'''
          ret rule (show ws ++ " \\leadsto " ++ show ws''') [drv]
    WJug (Sub ty@(TArr ty1 ty2) (ETVar a)) : ws'
      | a `notElem` toListOf fv ty -> do
          a1 <- fresh a
          a2 <- fresh a
          ws'' <- substWL a (TArr (ETVar a1) (ETVar a2)) [WTVar a1 ETVarBind, WTVar a2 ETVarBind] ws'
          let ws''' = WJug (Sub (TArr ty1 ty2) (TArr (ETVar a1) (ETVar a2))) : ws''
          drv <- infer "SubSplitR" ws'''
          ret rule (show ws ++ " \\leadsto " ++ show ws''') [drv]
    WJug (Sub (ETVar a) (ETVar b)) : ws' | before ws' a b -> do
      ws'' <- substWL b (ETVar a) [] ws'
      drv <- infer "SubInstETVar1" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (ETVar b) (ETVar a)) : ws' | before ws' a b -> do
      ws'' <- substWL b (ETVar a) [] ws'
      drv <- infer "SubInstETVar2" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (TVar a) (ETVar b)) : ws' | before ws' a b -> do
      ws'' <- substWL b (TVar a) [] ws'
      drv <- infer "SubInstETVar3" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (ETVar b) (TVar a)) : ws' | before ws' a b -> do
      ws'' <- substWL b (ETVar a) [] ws'
      drv <- infer "SubInstETVar4" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub TInt (ETVar b)) : ws' -> do
      ws'' <- substWL b TInt [] ws'
      drv <- infer "SubInstETVar5" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (ETVar b) TInt) : ws' -> do
      ws'' <- substWL b TInt [] ws'
      drv <- infer "SubInstETVar6" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub TBool (ETVar b)) : ws' -> do
      ws'' <- substWL b TBool [] ws'
      drv <- infer "SubInstETVar7" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (ETVar b) TBool) : ws' -> do
      ws'' <- substWL b TBool [] ws'
      drv <- infer "SubInstETVar8" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug End : ws' -> do
      drv <- infer "End" ws'
      ret rule (show ws ++ " \\leadsto " ++ show ws') [drv]
    WJug (Chk _ TTop) : ws' -> do
      drv <- infer "ChkTop" ws'
      ret rule (show ws ++ " \\leadsto " ++ show ws') [drv]
    WJug (Chk tm (TAll bnd)) : ws' -> do
      (a, ty) <- unbind bnd
      let ws'' = WJug (Chk tm ty) : WTVar a TVarBind : ws'
      drv <- infer "ChkAll" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Chk (Lam bnd) (TArr ty1 ty2)) : ws' -> do
      (x, e) <- unbind bnd
      let ws'' = WJug (Chk e ty2) : WVar x ty1 : ws'
      drv <- infer "ChkLam" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Chk (Lam bnd) (ETVar a)) : ws' -> do
      (x, e) <- unbind bnd
      a1 <- fresh a
      a2 <- fresh a
      ws'' <-
        substWL a (TArr (ETVar a1) (ETVar a2)) [WTVar a1 ETVarBind, WTVar a2 ETVarBind] $
          WJug (Chk e (ETVar a2)) : WVar x (ETVar a1) : ws'
      drv <- infer "ChkLamSplit" ws''
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
      case tm of -- to make my life easier
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
      let ws'' = WJug (Inf tm1 (bind a (InfApp (TVar a) tm2 j))) : ws'
      drv <- infer "InfApp" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Inf (TApp tm ty) j) : ws' -> do
      a <- freshTVar
      let ws'' = WJug (Inf tm (bind a (InfTApp (TVar a) ty j))) : ws'
      drv <- infer "InfTApp" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (InfTApp (TAll bnd) ty2 j) : ws' -> do
      (a, ty1) <- unbind bnd
      let ws'' = WJug (substBind j (subst a ty2 ty1)) : ws'
      drv <- infer "InfTAppAll" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (InfTApp TBot _ j) : ws' -> do
      let ws'' = WJug (substBind j TBot) : ws'
      drv <- infer "InfTAppBot" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (InfApp (TAll bnd) tm j) : ws' -> do
      (a, ty) <- unbind bnd
      let ws'' = WJug (InfApp (subst a (ETVar a) ty) tm j) : WTVar a ETVarBind : ws'
      drv <- infer "InfAppAll" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (InfApp (TArr ty1 ty2) tm j) : ws' -> do
      let ws'' = WJug (Chk tm ty1) : WJug (substBind j ty2) : ws'
      drv <- infer "InfAppArr" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (InfApp TBot _ j) : ws' -> do
      let ws'' = WJug (substBind j TBot) : ws'
      drv <- infer "InfAppBot" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (InfApp (ETVar a) tm j) : ws' -> do
      a1 <- fresh a
      a2 <- fresh a
      ws'' <-
        substWL a (TArr (ETVar a1) (ETVar a2)) [WTVar a1 ETVarBind, WTVar a2 ETVarBind] $
          WJug (InfApp (TArr (ETVar a1) (ETVar a2)) tm j) : ws'
      drv <- infer "InfAppETVar" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    _ -> throwError $ "\\text{No matching rule for } " ++ show ws
  where
    ret :: String -> String -> [Derivation] -> InferMonad Derivation
    ret ruleName expr drvs = do
      lift $ tell ["\\text{" ++ ruleName ++ ": } " ++ expr]
      return (Derivation ruleName expr drvs)

runElementary :: Trm -> InferResult
runElementary tm = case runInfer infer (initWL tm) of
  InferResult success finalType _ errorMsg errorLatex -> InferResult success finalType [] errorMsg errorLatex
