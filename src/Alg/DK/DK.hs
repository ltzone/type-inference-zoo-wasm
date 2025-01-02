{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Alg.DK.DK () where

import Control.Monad.Error.Class (MonadError (throwError))
import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Data.Foldable (find)
import Data.List (intercalate)
import Data.Tree (Tree (..))
import Lib (InferMonad, break3, freshTVar)
import Syntax (TmVar, Trm (..), TyVar, Typ (..), pattern TAll)
import Unbound.Generics.LocallyNameless (bind, subst, unbind)

data Entry
  = VarBnd TmVar Typ
  | TVarBnd TyVar
  | ETVarBnd TyVar
  | SETVarBnd TyVar Typ
  | Mark TyVar

type Ctx = [Entry]

instance Show Entry where
  show :: Entry -> String
  show (VarBnd x ty) = show x ++ ": " ++ show ty
  show (TVarBnd a) = show a
  show (ETVarBnd a) = "^" ++ show a
  show (SETVarBnd a ty) = "^" ++ show a ++ " = " ++ show ty
  show (Mark a) = "$" ++ show a

instance {-# OVERLAPPING #-} Show [Entry] where
  show :: [Entry] -> String
  show ctx = intercalate ", " $ map show ctx

appCtxTyp :: Ctx -> Typ -> InferMonad Typ
appCtxTyp _ (TVar a) = return $ TVar a
appCtxTyp _ TInt = return TInt
appCtxTyp _ TBool = return TBool
appCtxTyp ctx (ETVar a)
  | Just (SETVarBnd _ ty) <- find (\case SETVarBnd a' _ -> a == a'; _ -> False) ctx = return ty
  | otherwise = return $ ETVar a
appCtxTyp ctx (TArr ty1 ty2) = do
  ty1' <- appCtxTyp ctx ty1
  ty2' <- appCtxTyp ctx ty2
  return $ TArr ty1' ty2'
appCtxTyp ctx (TAll bnd) = do
  (a, ty) <- unbind bnd
  ty' <- appCtxTyp ctx ty
  return $ TAll (bind a ty')
appCtxTyp _ ty = error $ "appCtxTyp: not implemented for " ++ show ty

sub :: Ctx -> Typ -> Typ -> InferMonad (Ctx, Tree String)
sub = error "sub: not implemented"

check :: Ctx -> Trm -> Typ -> InferMonad (Ctx, Tree String)
check ctx tm ty = do
  lift $ tell ["Checking: " ++ showCheckIn]
  case (tm, ty) of
    (LitInt _, TInt) -> ret "ChkLitInt" ctx []
    (LitBool _, TBool) -> ret "ChkLitBool" ctx []
    (Lam bnd, TArr ty1 ty2) -> do
      (x, tm') <- unbind bnd
      (ctx', tree) <- check (VarBnd x ty1 : ctx) tm' ty2
      let (_, _, ctx2) = break3 (\case VarBnd x' _ -> x == x'; _ -> False) ctx'
      ret "ChkLam" ctx2 [tree]
    (tm', TAll bnd) -> do
      (a, ty') <- unbind bnd
      (ctx', tree) <- check (TVarBnd a : ctx) tm' ty'
      let (_, _, ctx2) = break3 (\case TVarBnd a' -> a == a'; _ -> False) ctx'
      ret "ChkAll" ctx2 [tree]
    _ -> do
      (ty1, ctx', tree1) <- infer ctx tm
      ty1' <- appCtxTyp ctx' ty1
      ty' <- appCtxTyp ctx' ty
      (ctx'', tree2) <- sub ctx' ty1' ty'
      ret "ChkSub" ctx'' [tree1, tree2]
  where
    showCheckIn = show ctx ++ " |- " ++ show tm ++ " ~ " ++ show ty
    showCheck ctx' = showCheckIn ++ " -| " ++ show ctx'

    ret :: String -> Ctx -> [Tree String] -> InferMonad (Ctx, Tree String)
    ret rule ctx' tree = do
      lift $ tell ["Checked[" ++ rule ++ "]: " ++ showCheck ctx']
      return (ctx', Node (rule ++ ": " ++ showCheck ctx') tree)

infer :: Ctx -> Trm -> InferMonad (Typ, Ctx, Tree String)
infer ctx tm = do
  lift $ tell ["Inferring: " ++ showInferIn]
  case tm of
    Var x -> case find (\case VarBnd x' _ -> x == x'; _ -> False) ctx of
      Just (VarBnd _ ty) -> ret "InfVar" ty ctx []
      _ -> throwError $ "Variable" ++ show x ++ " not found in context: " ++ show ctx
    Ann tm' ty -> do
      (ctx', tree) <- check ctx tm' ty
      ret "InfAnn" ty ctx' [tree]
    LitInt _ -> ret "InfLitInt" TInt ctx []
    LitBool _ -> ret "InfLitBool" TBool ctx []
    Lam bnd -> do
      (x, tm') <- unbind bnd
      a <- freshTVar
      b <- freshTVar
      let ctx' = VarBnd x (ETVar a) : ETVarBnd b : ETVarBnd a : ctx
      (ctx'', tree) <- check ctx' tm' (ETVar b)
      let (_, _, ctx2) = break3 (\case VarBnd x' _ -> x == x'; _ -> False) ctx''
      ret "InfLam" (TArr (TVar a) (TArr (ETVar a) (ETVar b))) ctx2 [tree]
    App tm1 tm2 -> do
      (ty1, ctx', tree1) <- infer ctx tm1
      ty1' <- appCtxTyp ctx' ty1
      (ty2, ctx'', tree2) <- inferApp ctx' ty1' tm2
      ret "InfApp" ty2 ctx'' [tree1, tree2]
    _ -> throwError $ "No rule matching: " ++ showInferIn
  where
    showInferIn = show ctx ++ " |- " ++ show tm
    showInfer ty' ctx' = showInferIn ++ " : " ++ show ty' ++ " -| " ++ show ctx'

    ret :: String -> Typ -> Ctx -> [Tree String] -> InferMonad (Typ, Ctx, Tree String)
    ret rule ty ctx' tree = do
      lift $ tell ["Inferred[" ++ rule ++ "]: " ++ showInfer ty ctx']
      return (ty, ctx', Node (rule ++ ": " ++ showInfer ty ctx') tree)

inferApp :: Ctx -> Typ -> Trm -> InferMonad (Typ, Ctx, Tree String)
inferApp ctx ty tm = do
  lift $ tell ["InferApp: " ++ showInferAppIn]
  case ty of
    TArr ty1 ty2 -> do
      (ctx', tree) <- check ctx tm ty1
      ret "InfAppArr" ty2 ctx' [tree]
    ETVar a -> do
      a1 <- freshTVar
      a2 <- freshTVar
      let (ctx1, _, ctx2) = break3 (\case ETVarBnd a' -> a == a'; _ -> False) ctx
          ctx' = ctx1 ++ SETVarBnd a (TArr (ETVar a1) (ETVar a2)) : ETVarBnd a1 : ETVarBnd a2 : ctx2
      (ctx'', tree) <- check ctx' tm (ETVar a1)
      ret "InfAppETVar" (ETVar a2) ctx'' [tree]
    TAll bnd -> do
      (a, ty') <- unbind bnd
      (ctx', tree) <- check ctx tm (subst a (ETVar a) ty')
      ret "InfAppAll" (subst a (ETVar a) ty') ctx' [tree]
    _ -> throwError $ "No rule matching: " ++ showInferAppIn
  where
    showInferAppIn = show ctx ++ " |- " ++ show tm ++ " * " ++ show ty
    showInferApp ty' ctx' = showInferAppIn ++ " ==>> " ++ show ty' ++ " -| " ++ show ctx'

    ret :: String -> Typ -> Ctx -> [Tree String] -> InferMonad (Typ, Ctx, Tree String)
    ret rule ty' ctx' trees = do
      lift $ tell ["InferredApp[" ++ rule ++ "]: " ++ showInferApp ty' ctx']
      return (ty', ctx', Node (rule ++ ": " ++ showInferApp ty' ctx') trees)
