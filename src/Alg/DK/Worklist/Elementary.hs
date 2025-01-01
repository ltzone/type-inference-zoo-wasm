{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Alg.DK.Worklist.Elementary (runElementary) where

import Alg.DK.Common (isAll)
import Alg.DK.Worklist.Common (Entry (..), Judgment (..), TBind (..), Worklist, before, substWL)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Data.Foldable (find)
import Lib (InferMonad, freshTVar, runInferMonad)
import Syntax (Trm (..), Typ (..))
import Unbound.Generics.LocallyNameless
  ( Fresh (fresh),
    Subst (subst),
    bind,
    fv,
    s2n,
    substBind,
    unbind,
  )
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

infer :: String -> Worklist -> InferMonad ()
infer rule ws = do
  lift $ tell [rule ++ ": " ++ show ws]
  case ws of
    [] -> return ()
    WTVar _ _ : ws' -> infer "GCTVar" ws'
    WVar _ _ : ws' -> infer "GCVar" ws'
    WJug (Sub TInt TInt) : ws' -> infer "SubInt" ws'
    WJug (Sub TBool TBool) : ws' -> infer "SubBool" ws'
    WJug (Sub (TVar a) (TVar b)) : ws' | a == b -> infer "SubReflTVar" ws'
    WJug (Sub (ETVar a) (ETVar b)) : ws' | a == b -> infer "SubReflETVar" ws'
    WJug (Sub (STVar a) (STVar b)) : ws' | a == b -> infer "SubReflSTVar" ws'
    WJug (Sub _ TTop) : ws' -> infer "SubTop" ws'
    WJug (Sub TBot _) : ws' -> infer "SubBot" ws'
    WJug (Sub (TArr ty1 ty2) (TArr ty1' ty2')) : ws' ->
      infer "SubArr" $ WJug (Sub ty1' ty1) : WJug (Sub ty2 ty2') : ws'
    WJug (Sub (TAll bnd) ty2) : ws' | not (isAll ty2) -> do
      -- ty2 is not Top as well
      (a, ty1) <- unbind bnd
      let ty1' = subst a (ETVar a) ty1
      infer "SubAllL" $ WJug (Sub ty1' ty2) : WTVar a ETVarBind : ws'
    WJug (Sub (TAll bnd1) (TAll bnd2)) : ws' -> do
      a <- freshTVar
      let ty1 = substBind bnd1 (ETVar a)
          ty2 = substBind bnd2 (ETVar a)
      infer "SubAllR" $ WJug (Sub ty1 ty2) : WTVar a STVarBind : ws'
    WJug (Sub (ETVar a) ty@(TArr ty1 ty2)) : ws'
      | a `notElem` toListOf fv ty -> do
          a1 <- fresh a
          a2 <- fresh a
          ws'' <- substWL a (TArr (ETVar a1) (ETVar a2)) [WTVar a1 ETVarBind, WTVar a2 ETVarBind] ws'
          infer "SubSplitL" $ WJug (Sub (TArr (ETVar a1) (ETVar a2)) (TArr ty1 ty2)) : ws''
    WJug (Sub ty@(TArr ty1 ty2) (ETVar a)) : ws'
      | a `notElem` toListOf fv ty -> do
          a1 <- fresh a
          a2 <- fresh a
          ws'' <- substWL a (TArr (ETVar a1) (ETVar a2)) [WTVar a1 ETVarBind, WTVar a2 ETVarBind] ws'
          infer "SubSplitR" $ WJug (Sub (TArr ty1 ty2) (TArr (ETVar a1) (ETVar a2))) : ws''
    WJug (Sub (ETVar a) (ETVar b)) : ws' | before ws' a b -> do
      ws'' <- substWL b (ETVar a) [] ws'
      infer "SubInstETVar1" ws''
    WJug (Sub (ETVar b) (ETVar a)) : ws' | before ws' a b -> do
      ws'' <- substWL b (ETVar a) [] ws'
      infer "SubInstETVar2" ws''
    WJug (Sub (TVar a) (ETVar b)) : ws' | before ws' a b -> do
      ws'' <- substWL b (TVar a) [] ws'
      infer "SubInstETVar3" ws''
    WJug (Sub (ETVar b) (TVar a)) : ws' | before ws' a b -> do
      ws'' <- substWL b (ETVar a) [] ws'
      infer "SubInstETVar4" ws''
    WJug (Sub TInt (ETVar b)) : ws' -> do
      ws'' <- substWL b TInt [] ws'
      infer "SubInstETVar5" ws''
    WJug (Sub (ETVar b) TInt) : ws' -> do
      ws'' <- substWL b TInt [] ws'
      infer "SubInstETVar6" ws''
    WJug (Sub TBool (ETVar b)) : ws' -> do
      ws'' <- substWL b TBool [] ws'
      infer "SubInstETVar7" ws''
    WJug (Sub (ETVar b) TBool) : ws' -> do
      ws'' <- substWL b TBool [] ws'
      infer "SubInstETVar8" ws''
    WJug End : ws' -> infer "End" ws'
    WJug (Chk _ TTop) : ws' -> infer "ChkTop" ws'
    WJug (Chk tm (TAll bnd)) : ws' -> do
      (a, ty) <- unbind bnd
      infer "ChkAll" $ WJug (Chk tm ty) : WTVar a TVarBind : ws'
    WJug (Chk (Lam bnd) (TArr ty1 ty2)) : ws' -> do
      (x, e) <- unbind bnd
      infer "ChkLam" $ WJug (Chk e ty2) : WVar x ty1 : ws'
    WJug (Chk (Lam bnd) (ETVar a)) : ws' -> do
      (x, e) <- unbind bnd
      a1 <- fresh a
      a2 <- fresh a
      ws'' <-
        substWL a (TArr (ETVar a1) (ETVar a2)) [WTVar a1 ETVarBind, WTVar a2 ETVarBind] $
          WJug (Chk e (ETVar a2)) : WVar x (ETVar a1) : ws'
      infer "ChkLamSplit" ws''
    WJug (Chk tm ty) : ws' -> do
      a <- freshTVar
      infer "ChkSub" $ WJug (Inf tm (bind a (Sub (TVar a) ty))) : ws'
    WJug (Inf (Var x) j) : ws' -> do
      case find (\case WVar x' _ -> x == x'; _ -> False) ws' of
        Just (WVar _ ty) -> infer "InfVar" $ WJug (substBind j ty) : ws'
        _ -> throwError $ show x ++ " is not found"
    WJug (Inf (Ann tm ty) j) : ws' ->
      infer "InfAnn" $ WJug (Chk tm ty) : WJug (substBind j ty) : ws'
    WJug (Inf (TLam bnd) j) : ws' -> do
      (a, tm) <- unbind bnd
      case tm of -- to make my life easier
        Ann tm' ty ->
          infer "InfTLam" $
            WJug (Chk tm' ty)
              : WTVar a TVarBind
              : WJug (substBind j (TAll (bind a ty)))
              : ws'
        _ -> throwError $ show tm ++ " is not an annotated term"
    WJug (Inf (LitInt _) j) : ws' ->
      infer "InfLitInt" $ WJug (substBind j TInt) : ws'
    WJug (Inf (LitBool _) j) : ws' ->
      infer "InfLitBool" $ WJug (substBind j TBool) : ws'
    WJug (Inf (Lam bnd) j) : ws' -> do
      a <- freshTVar
      b <- freshTVar
      (x, e) <- unbind bnd
      infer "InfLam" $
        WJug (Chk e (ETVar b))
          : WVar x (ETVar a)
          : WJug (substBind j (TArr (ETVar a) (ETVar b)))
          : WTVar a ETVarBind
          : WTVar b ETVarBind
          : ws'
    WJug (Inf (App tm1 tm2) j) : ws' -> do
      a <- freshTVar
      infer "InfApp" $ WJug (Inf tm1 (bind a (InfApp (TVar a) tm2 j))) : ws'
    WJug (Inf (TApp tm ty) j) : ws' -> do
      a <- freshTVar
      infer "InfTApp" $ WJug (Inf tm (bind a (InfTApp (TVar a) ty j))) : ws'
    WJug (InfTApp (TAll bnd) ty2 j) : ws' -> do
      (a, ty1) <- unbind bnd
      infer "InfTAppAll" $ WJug (substBind j (subst a ty2 ty1)) : ws'
    WJug (InfTApp TBot _ j) : ws' ->
      infer "InfTAppBot" $ WJug (substBind j TBot) : ws'
    WJug (InfApp (TAll bnd) tm j) : ws' -> do
      (a, ty) <- unbind bnd
      infer "InfAppAll" $ WJug (InfApp (subst a (ETVar a) ty) tm j) : WTVar a ETVarBind : ws'
    WJug (InfApp (TArr ty1 ty2) tm j) : ws' ->
      infer "InfAppArr" $ WJug (Chk tm ty1) : WJug (substBind j ty2) : ws'
    WJug (InfApp TBot _ j) : ws' ->
      infer "InfAppBot" $ WJug (substBind j TBot) : ws'
    WJug (InfApp (ETVar a) tm j) : ws' -> do
      a1 <- fresh a
      a2 <- fresh a
      ws'' <-
        substWL a (TArr (ETVar a1) (ETVar a2)) [WTVar a1 ETVarBind, WTVar a2 ETVarBind] $
          WJug (InfApp (TArr (ETVar a1) (ETVar a2)) tm j) : ws'
      infer "InfAppETVar" ws''
    _ -> throwError $ "No matching rule for " ++ show ws

runInfer :: Worklist -> Either [String] [String]
runInfer ws = case runInferMonad $ infer "Init" ws of
  Left errs -> Left errs
  Right (_, msgs) -> Right msgs

runElementary :: Trm -> Either [String] [String]
runElementary tm = runInfer [WJug (Inf tm (bind (s2n "_") End))]
