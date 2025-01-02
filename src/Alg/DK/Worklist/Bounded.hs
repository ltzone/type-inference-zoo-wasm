{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Alg.DK.Worklist.Bounded (runBounded) where

import Alg.DK.Common (isAllB, isLam)
import Alg.DK.Worklist.Common (Entry (..), Judgment (..), TBind (..), Worklist, initWL, runInfer, substWLOrd)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Data.Foldable (find)
import Lib (InferMonad, freshTVar)
import Syntax (Trm (..), Typ (..))
import Unbound.Generics.LocallyNameless
  ( Fresh (fresh),
    Subst (subst),
    aeq,
    bind,
    fv,
    substBind,
    unbind,
  )
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

mono :: Worklist -> Typ -> Bool
-- TODO: we should be careful about the wildcard when extending more types
mono _ TInt = True
mono _ TBool = True
mono ws (TArr ty1 ty2) = mono ws ty1 && mono ws ty2
mono _ (ETVar _) = True
mono ws (TVar a) = case find (\case WTVar a' (TVarBBind TTop) -> a == a'; _ -> False) ws of
  Just _ -> True
  Nothing -> False
mono _ _ = False

infer :: String -> Worklist -> InferMonad ()
infer rule ws = do
  lift $ tell [rule ++ ": " ++ show ws]
  case ws of
    [] -> return ()
    WTVar _ _ : ws' -> infer "GCTVar" ws'
    WVar _ _ : ws' -> infer "GCVar" ws'
    WJug (Sub TInt TInt) : ws' -> infer "SubReflInt" ws'
    WJug (Sub TBool TBool) : ws' -> infer "SubReflBool" ws'
    WJug (Sub (TVar a) (TVar b)) : ws' | a == b -> infer "SubReflTVar" ws'
    WJug (Sub (ETVar a) (ETVar b)) : ws' | a == b -> infer "SubReflETVar" ws'
    WJug (Sub (STVar a) (STVar b)) : ws' | a == b -> infer "SubReflSTVar" ws'
    WJug (Sub _ TTop) : ws' -> infer "SubTop" ws'
    WJug (Sub TBot _) : ws' -> infer "SubBot" ws'
    WJug (Sub ty1@(TVar a) ty2) : ws'
      | Just (WTVar _ (TVarBBind b)) <-
          find (\case WTVar a' _ -> a == a'; _ -> False) ws',
        not (aeq ty1 ty2),
        not (aeq b TTop) ->
          infer "SubTVarTrans" $ WJug (Sub b ty2) : ws'
    WJug (Sub ty1@(STVar a) ty2) : ws'
      | Just (WTVar _ (STVarBBind b)) <-
          find (\case WTVar a' _ -> a == a'; _ -> False) ws',
        not (aeq ty1 ty2),
        not (aeq b TTop) ->
          infer "SubSTVarTrans" $ WJug (Sub b ty2) : ws'
    WJug (Sub (TArr ty1 ty2) (TArr ty1' ty2')) : ws' ->
      infer "SubArr" $ WJug (Sub ty1' ty1) : WJug (Sub ty2 ty2') : ws'
    WJug (Sub (TAllB bnd b) ty2) : ws' | not (isAllB ty2) -> do
      -- ty2 is not Top as well
      (a, ty1) <- unbind bnd
      let ty1' = subst a (ETVar a) ty1
      infer "SubAllL" $
        WJug (Sub ty1' ty2)
          : WJug (Sub (ETVar a) b)
          : WTVar a ETVarBind
          : ws'
    WJug (Sub (TAllB bnd1 b1) (TAllB bnd2 b2)) : ws' -> do
      a <- freshTVar
      let ty1 = substBind bnd1 (ETVar a)
          ty2 = substBind bnd2 (ETVar a)
      infer "SubAll" $
        WJug (Sub ty1 ty2)
          : WJug (Sub b1 b2)
          : WJug (Sub b2 b1)
          : WTVar a (STVarBBind b1)
          : ws'
    WJug (Sub (ETVar a) ty) : ws' | mono ws ty -> do
      ws'' <- substWLOrd a ty ws'
      infer "SubInstETVar" ws''
    WJug (Sub ty (ETVar a)) : ws' | mono ws ty -> do
      ws'' <- substWLOrd a ty ws'
      infer "SubInstETVar" ws''
    WJug (Sub (ETVar a) ty@(TArr ty1 ty2)) : ws'
      | a `notElem` toListOf fv ty -> do
          a1 <- fresh a
          a2 <- fresh a
          ws'' <-
            substWLOrd a (TArr (ETVar a1) (ETVar a2)) $
              WTVar a1 ETVarBind : WTVar a2 ETVarBind : ws'
          infer "SubSplitL" $ WJug (Sub (TArr (ETVar a1) (ETVar a2)) (TArr ty1 ty2)) : ws''
    WJug (Sub ty@(TArr ty1 ty2) (ETVar a)) : ws'
      | a `notElem` toListOf fv ty -> do
          a1 <- fresh a
          a2 <- fresh a
          ws'' <-
            substWLOrd a (TArr (ETVar a1) (ETVar a2)) $
              WTVar a1 ETVarBind : WTVar a2 ETVarBind : ws'
          infer "SubSplitR" $ WJug (Sub (TArr ty1 ty2) (TArr (ETVar a1) (ETVar a2))) : ws''
    WJug End : ws' -> infer "End" ws'
    WJug (Chk (Lam bnd) TTop) : ws' -> do
      (x, e) <- unbind bnd
      infer "ChkLamTop" $ WJug (Chk e TTop) : WVar x TBot : ws'
    WJug (Chk (Lam bnd) (TArr ty1 ty2)) : ws' -> do
      (x, e) <- unbind bnd
      infer "ChkLam" $ WJug (Chk e ty2) : WVar x ty1 : ws'
    entry@(WJug (Chk (Lam bnd) (ETVar a))) : ws' -> do
      (x, e) <- unbind bnd
      a1 <- fresh a
      a2 <- fresh a
      ws'' <-
        substWLOrd a (TArr (ETVar a1) (ETVar a2)) $
          entry : WJug (Chk e (ETVar a2)) : WVar x (ETVar a1) : ws'
      infer "ChkLamSplit" ws''
    WJug (Chk tm ty) : ws' | not $ isLam tm -> do
      a <- freshTVar
      infer "ChkSub" $ WJug (Inf tm (bind a (Sub (TVar a) ty))) : ws'
    WJug (Inf (Var x) j) : ws' -> do
      case find (\case WVar x' _ -> x == x'; _ -> False) ws' of
        Just (WVar _ ty) -> infer "InfVar" $ WJug (substBind j ty) : ws'
        _ -> throwError $ show x ++ " is not found"
    WJug (Inf (Ann tm ty) j) : ws' ->
      infer "InfAnn" $ WJug (Chk tm ty) : WJug (substBind j ty) : ws'
    WJug (Inf (TLamB bnd b) j) : ws' -> do
      (a, tm) <- unbind bnd
      case tm of -- to make my life easier
        Ann tm' ty ->
          infer "InfTLam" $
            WJug (Chk tm' ty)
              : WTVar a (TVarBBind b)
              : WJug (substBind j (TAllB (bind a ty) b))
              : ws'
        _ -> throwError $ show tm ++ " is not an annotated term"
    WJug (Inf (LitInt _) j) : ws' ->
      infer "InfLitInt" $ WJug (substBind j TInt) : ws'
    WJug (Inf (LitBool _) j) : ws' ->
      infer "InfLitBool" $ WJug (substBind j TBool) : ws'
    WJug (Inf (App tm1 tm2) j) : ws' -> do
      a <- freshTVar
      b <- freshTVar
      let j' = Inf tm1 $ bind a $ Match (TVar a) $ bind b $ InfApp (TVar b) tm2 j
      infer "InfApp" $ WJug j' : ws'
    WJug (Inf (TApp tm ty) j) : ws' -> do
      a <- freshTVar
      infer "InfTApp" $ WJug (Inf tm (bind a (InfTApp (TVar a) ty j))) : ws'
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
    WJug (Match ty@(TArr _ _) j) : ws' ->
      infer "MatchArr" $ WJug (substBind j ty) : ws'
    WJug (Match TBot j) : ws' ->
      infer "MatchBot" $ WJug (substBind j (TArr TBot TBot)) : ws'
    WJug (Match (TAllB bnd b) j) : ws' -> do
      (a, ty) <- unbind bnd
      let j' = Match (subst a (ETVar a) ty) j
      infer "MatchAll" $ WJug j' : WJug (Sub (ETVar a) b) : WTVar a ETVarBind : ws'
    WJug (Match (TVar a) j) : ws'
      | Just (WTVar _ (TVarBBind b)) <-
          find (\case WTVar a' _ -> a == a'; _ -> False) ws' ->
          infer "MatchTVar" $ WJug (Match b j) : ws'
    entry@(WJug (Match (ETVar a) _)) : ws' -> do
      a1 <- fresh a
      a2 <- fresh a
      ws'' <-
        substWLOrd a (TArr (ETVar a1) (ETVar a2)) $
          entry : WTVar a1 ETVarBind : WTVar a2 ETVarBind : ws'
      infer "MatchETVar" ws''
    WJug (InfApp (TArr ty1 ty2) tm j) : ws' ->
      infer "InfApp" $ WJug (Chk tm ty1) : WJug (substBind j ty2) : ws'
    WJug (InfTApp (TAllB bnd b) ty2 j) : ws' -> do
      (a, ty1) <- unbind bnd
      let j1 = substBind j (subst a ty2 ty1)
          j2 = Sub ty2 b
      infer "InfTAppAll" $ WJug j1 : WJug j2 : ws'
    WJug (InfTApp TBot _ j) : ws' ->
      infer "InfTAppBot" $ WJug (substBind j TBot) : ws'
    WJug (InfTApp (TVar a) ty2 j) : ws'
      | Just (WTVar _ (TVarBBind ty1)) <-
          find (\case WTVar a' _ -> a == a'; _ -> False) ws' ->
          infer "InfTAppTVar" $ WJug (InfTApp ty1 ty2 j) : ws'
    _ -> throwError $ "No matching rule for " ++ show ws

runBounded :: Trm -> Either [String] [String]
runBounded = runInfer infer . initWL
