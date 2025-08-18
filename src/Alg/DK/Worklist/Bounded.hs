{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Alg.DK.Worklist.Bounded (runBounded) where

import Alg.DK.Common (isAllB, isLam)
import Alg.DK.Worklist.Common (Entry (..), Judgment (..), TBind (..), Worklist, initWL, runInfer, substWLOrd)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Data.Foldable (find)
import Lib (Derivation (..), InferMonad, InferResult (..), freshTVar)
import Syntax (Trm (..), Typ (..), latexifyVar)
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
    WJug (Sub ty1@(TVar a) ty2) : ws'
      | Just (WTVar _ (TVarBBind b)) <-
          find (\case WTVar a' _ -> a == a'; _ -> False) ws',
        not (aeq ty1 ty2),
        not (aeq b TTop) -> do
          let ws'' = WJug (Sub b ty2) : ws'
          drv <- infer "SubTVarTrans" ws''
          ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub ty1@(STVar a) ty2) : ws'
      | Just (WTVar _ (STVarBBind b)) <-
          find (\case WTVar a' _ -> a == a'; _ -> False) ws',
        not (aeq ty1 ty2),
        not (aeq b TTop) -> do
          let ws'' = WJug (Sub b ty2) : ws'
          drv <- infer "SubSTVarTrans" ws''
          ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (TArr ty1 ty2) (TArr ty1' ty2')) : ws' -> do
      let ws'' = WJug (Sub ty1' ty1) : WJug (Sub ty2 ty2') : ws'
      drv <- infer "SubArr" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (TAllB bnd b) ty2) : ws' | not (isAllB ty2) -> do
      -- ty2 is not Top as well
      (a, ty1) <- unbind bnd
      let ty1' = subst a (ETVar a) ty1
          ws'' = WJug (Sub ty1' ty2)
                   : WJug (Sub (ETVar a) b)
                   : WTVar a ETVarBind
                   : ws'
      drv <- infer "SubAllL" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (TAllB bnd1 b1) (TAllB bnd2 b2)) : ws' -> do
      a <- freshTVar
      let ty1 = substBind bnd1 (ETVar a)
          ty2 = substBind bnd2 (ETVar a)
          ws'' = WJug (Sub ty1 ty2)
                   : WJug (Sub b1 b2)
                   : WJug (Sub b2 b1)
                   : WTVar a (STVarBBind b1)
                   : ws'
      drv <- infer "SubAll" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (ETVar a) ty) : ws'
      | a `notElem` toListOf fv ty,
        mono ws ty -> do
          ws'' <- substWLOrd a ty ws'
          drv <- infer "SubInstETVar" ws''
          ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub ty (ETVar a)) : ws'
      | a `notElem` toListOf fv ty,
        mono ws ty -> do
          ws'' <- substWLOrd a ty ws'
          drv <- infer "SubInstETVar" ws''
          ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Sub (ETVar a) ty@(TArr ty1 ty2)) : ws'
      | a `notElem` toListOf fv ty -> do
          a1 <- fresh a
          a2 <- fresh a
          ws'' <-
            substWLOrd a (TArr (ETVar a1) (ETVar a2)) $
              WTVar a1 ETVarBind : WTVar a2 ETVarBind : ws'
          let ws''' = WJug (Sub (TArr (ETVar a1) (ETVar a2)) (TArr ty1 ty2)) : ws''
          drv <- infer "SubSplitL" ws'''
          ret rule (show ws ++ " \\leadsto " ++ show ws''') [drv]
    WJug (Sub ty@(TArr ty1 ty2) (ETVar a)) : ws'
      | a `notElem` toListOf fv ty -> do
          a1 <- fresh a
          a2 <- fresh a
          ws'' <-
            substWLOrd a (TArr (ETVar a1) (ETVar a2)) $
              WTVar a1 ETVarBind : WTVar a2 ETVarBind : ws'
          let ws''' = WJug (Sub (TArr ty1 ty2) (TArr (ETVar a1) (ETVar a2))) : ws''
          drv <- infer "SubSplitR" ws'''
          ret rule (show ws ++ " \\leadsto " ++ show ws''') [drv]
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
    entry@(WJug (Chk (Lam bnd) (ETVar a))) : ws' -> do
      (x, e) <- unbind bnd
      a1 <- fresh a
      a2 <- fresh a
      ws'' <-
        substWLOrd a (TArr (ETVar a1) (ETVar a2)) $
          entry : WJug (Chk e (ETVar a2)) : WVar x (ETVar a1) : ws'
      drv <- infer "ChkLamSplit" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Chk tm ty) : ws' | not $ isLam tm -> do
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
    WJug (Inf (TLamB bnd b) j) : ws' -> do
      (a, tm) <- unbind bnd
      case tm of -- to make my life easier
        Ann tm' ty -> do
          let ws'' = WJug (Chk tm' ty)
                       : WTVar a (TVarBBind b)
                       : WJug (substBind j (TAllB (bind a ty) b))
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
    WJug (Inf (App tm1 tm2) j) : ws' -> do
      a <- freshTVar
      b <- freshTVar
      let j' = Inf tm1 $ bind a $ Match (TVar a) $ bind b $ InfApp (TVar b) tm2 j
          ws'' = WJug j' : ws'
      drv <- infer "InfApp" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Inf (TApp tm ty) j) : ws' -> do
      a <- freshTVar
      let ws'' = WJug (Inf tm (bind a (InfTApp (TVar a) ty j))) : ws'
      drv <- infer "InfTApp" ws''
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
    WJug (Match ty@(TArr _ _) j) : ws' -> do
      let ws'' = WJug (substBind j ty) : ws'
      drv <- infer "MatchArr" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Match TBot j) : ws' -> do
      let ws'' = WJug (substBind j (TArr TBot TBot)) : ws'
      drv <- infer "MatchBot" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Match (TAllB bnd b) j) : ws' -> do
      (a, ty) <- unbind bnd
      let j' = Match (subst a (ETVar a) ty) j
          ws'' = WJug j' : WJug (Sub (ETVar a) b) : WTVar a ETVarBind : ws'
      drv <- infer "MatchAll" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (Match (TVar a) j) : ws'
      | Just (WTVar _ (TVarBBind b)) <-
          find (\case WTVar a' _ -> a == a'; _ -> False) ws' -> do
          let ws'' = WJug (Match b j) : ws'
          drv <- infer "MatchTVar" ws''
          ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    entry@(WJug (Match (ETVar a) _)) : ws' -> do
      a1 <- fresh a
      a2 <- fresh a
      ws'' <-
        substWLOrd a (TArr (ETVar a1) (ETVar a2)) $
          entry : WTVar a1 ETVarBind : WTVar a2 ETVarBind : ws'
      drv <- infer "MatchETVar" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (InfApp (TArr ty1 ty2) tm j) : ws' -> do
      let ws'' = WJug (Chk tm ty1) : WJug (substBind j ty2) : ws'
      drv <- infer "InfApp" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (InfTApp (TAllB bnd b) ty2 j) : ws' -> do
      (a, ty1) <- unbind bnd
      let j1 = substBind j (subst a ty2 ty1)
          j2 = Sub ty2 b
          ws'' = WJug j1 : WJug j2 : ws'
      drv <- infer "InfTAppAll" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (InfTApp TBot _ j) : ws' -> do
      let ws'' = WJug (substBind j TBot) : ws'
      drv <- infer "InfTAppBot" ws''
      ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    WJug (InfTApp (TVar a) ty2 j) : ws'
      | Just (WTVar _ (TVarBBind ty1)) <-
          find (\case WTVar a' _ -> a == a'; _ -> False) ws' -> do
          let ws'' = WJug (InfTApp ty1 ty2 j) : ws'
          drv <- infer "InfTAppTVar" ws''
          ret rule (show ws ++ " \\leadsto " ++ show ws'') [drv]
    _ -> throwError $ "\\text{No matching rule for } " ++ show ws
  where
    ret :: String -> String -> [Derivation] -> InferMonad Derivation
    ret ruleName expr drvs = do
      lift $ tell ["\\text{" ++ ruleName ++ ": } " ++ expr]
      return (Derivation ruleName expr drvs)

runBounded :: Trm -> InferResult
runBounded tm = case runInfer infer (initWL tm) of
  InferResult success finalType _ errorMsg errorLatex -> InferResult success finalType [] errorMsg errorLatex
