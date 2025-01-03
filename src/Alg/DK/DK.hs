{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Alg.DK.DK (runDK) where

import Alg.DK.Common (isAll)
import Control.Monad.Error.Class (MonadError (throwError))
import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Data.Foldable (find)
import Data.List (intercalate)
import Data.Tree (Tree (..))
import Lib (InferMonad, break3, freshTVar, runInferMonad)
import Syntax (TmVar, Trm (..), TyVar, Typ (..), pattern TAll)
import Unbound.Generics.LocallyNameless (bind, fv, subst, unbind)
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

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

mono :: Typ -> Bool
mono TInt = True
mono TBool = True
mono (TVar _) = True
mono (ETVar _) = True
mono (TArr ty1 ty2) = mono ty1 && mono ty2
mono (TAll _) = False
mono ty = error $ "mono: not implemented for " ++ show ty

appCtxTyp :: Ctx -> Typ -> InferMonad Typ
appCtxTyp ctx ty = do
  lift $ tell ["Substituting: " ++ showAppCtxTypIn]
  case ty of
    TVar a -> ret $ TVar a
    TInt -> ret TInt
    TBool -> ret TBool
    ETVar a
      | Just (SETVarBnd _ ty') <- find (\case SETVarBnd a' _ -> a == a'; _ -> False) ctx -> ret ty'
      | otherwise -> ret $ ETVar a
    TArr ty1 ty2 -> do
      ty1' <- appCtxTyp ctx ty1
      ty2' <- appCtxTyp ctx ty2
      ret $ TArr ty1' ty2'
    TAll bnd -> do
      (a, ty') <- unbind bnd
      ty'' <- appCtxTyp ctx ty'
      ret $ TAll (bind a ty'')
    _ -> throwError $ "appCtxTyp: not implemented for " ++ show ty
  where
    showAppCtxTypIn = "[" ++ show ctx ++ "](" ++ show ty ++ ")"
    showAppCtxTyp ty' = "[" ++ show ctx ++ "](" ++ show ty ++ ") = " ++ show ty'

    ret :: Typ -> InferMonad Typ
    ret ty' = do
      lift $ tell ["Substituted: " ++ showAppCtxTyp ty']
      return ty'

before :: Ctx -> TyVar -> TyVar -> Bool
before ws a b =
  let (ws1, _) = break (\case ETVarBnd a' -> a == a'; _ -> False) ws
      (ws1', _) = break (\case ETVarBnd b' -> b == b'; _ -> False) ws
   in length ws1 > length ws1'

instL :: Ctx -> TyVar -> Typ -> InferMonad (Ctx, Tree String)
instL ctx a ty = do
  lift $ tell ["InstL: " ++ showInstLIn]
  case ty of
    ETVar b | before ctx a b -> do
      let (ctx1, _, ctx2) = break3 (\case ETVarBnd b' -> b == b'; _ -> False) ctx
      ret "InstLReach" (ctx1 ++ SETVarBnd b (ETVar a) : ctx2) []
    TArr ty1 ty2 -> do
      a1 <- freshTVar
      a2 <- freshTVar
      let (ctx1, _, ctx2) = break3 (\case ETVarBnd a' -> a == a'; _ -> False) ctx
          ctx' = ctx1 ++ SETVarBnd a (TArr (ETVar a1) (ETVar a2)) : ETVarBnd a1 : ETVarBnd a2 : ctx2
      (ctx'', tree1) <- instR ctx' ty1 a1
      ty2' <- appCtxTyp ctx'' ty2
      (ctx''', tree2) <- instL ctx'' a2 ty2'
      ret "InstLArr" ctx''' [tree1, tree2]
    TAll bnd -> do
      (b, ty') <- unbind bnd
      (ctx', tree) <- instL (TVarBnd b : ctx) a ty'
      let (_, _, ctx2) = break3 (\case TVarBnd b' -> b == b'; _ -> False) ctx'
      ret "InstLAllR" ctx2 [tree]
    _ | mono ty -> do
      let (ctx1, _, ctx2) = break3 (\case ETVarBnd a' -> a == a'; _ -> False) ctx
      ret "InstLSolve" (ctx1 ++ SETVarBnd a ty : ctx2) []
    _ -> throwError $ "No rule matching: " ++ showInstLIn
  where
    showInstLIn = show ctx ++ " |- ^" ++ show a ++ " :=< " ++ show ty
    showInstL ctx' = showInstLIn ++ " -| " ++ show ctx'

    ret :: String -> Ctx -> [Tree String] -> InferMonad (Ctx, Tree String)
    ret rule ctx' tree = do
      lift $ tell ["InstL[" ++ rule ++ "]: " ++ showInstL ctx']
      return (ctx', Node (rule ++ ": " ++ showInstL ctx') tree)

instR :: Ctx -> Typ -> TyVar -> InferMonad (Ctx, Tree String)
instR ctx ty a = do
  lift $ tell ["InstR: " ++ showInstRIn]
  case ty of
    ETVar b | before ctx a b -> do
      let (ctx1, _, ctx2) = break3 (\case ETVarBnd b' -> b == b'; _ -> False) ctx
      ret "InstRReach" (ctx1 ++ SETVarBnd b (ETVar a) : ctx2) []
    TArr ty1 ty2 -> do
      a1 <- freshTVar
      a2 <- freshTVar
      let (ctx1, _, ctx2) = break3 (\case ETVarBnd a' -> a == a'; _ -> False) ctx
          ctx' = ctx1 ++ SETVarBnd a (TArr (ETVar a1) (ETVar a2)) : ETVarBnd a1 : ETVarBnd a2 : ctx2
      (ctx'', tree1) <- instL ctx' a1 ty1
      ty2' <- appCtxTyp ctx'' ty2
      (ctx''', tree2) <- instR ctx'' ty2' a2
      ret "InstRArr" ctx''' [tree1, tree2]
    TAll bnd -> do
      (b, ty') <- unbind bnd
      let ty'' = subst b (ETVar b) ty'
      (ctx', tree) <- instR (ETVarBnd b : Mark b : ctx) ty'' a
      let (_, _, ctx2) = break3 (\case Mark b' -> b == b'; _ -> False) ctx'
      ret "InstRAllL" ctx2 [tree]
    _ | mono ty -> do
      let (ctx1, _, ctx2) = break3 (\case ETVarBnd a' -> a == a'; _ -> False) ctx
      ret "InstRSolve" (ctx1 ++ SETVarBnd a ty : ctx2) []
    _ -> throwError $ "No rule matching: " ++ showInstRIn
  where
    showInstRIn = show ctx ++ " |- " ++ show ty ++ " :=< ^" ++ show a
    showInstR ctx' = showInstRIn ++ " -| " ++ show ctx'

    ret :: String -> Ctx -> [Tree String] -> InferMonad (Ctx, Tree String)
    ret rule ctx' tree = do
      lift $ tell ["InstR[" ++ rule ++ "]: " ++ showInstR ctx']
      return (ctx', Node (rule ++ ": " ++ showInstR ctx') tree)

sub :: Ctx -> Typ -> Typ -> InferMonad (Ctx, Tree String)
sub ctx ty1 ty2 = do
  lift $ tell ["Subtyping: " ++ showSubIn]
  case (ty1, ty2) of
    (TInt, TInt) -> ret "SubInt" ctx []
    (TBool, TBool) -> ret "SubBool" ctx []
    (TVar a, TVar b) | a == b -> ret "SubReflTVar" ctx []
    (ETVar a, ETVar b) | a == b -> ret "SubReflETVar" ctx []
    (TArr ty1' ty2', TArr ty1'' ty2'') -> do
      (ctx1, tree1) <- sub ctx ty1'' ty1'
      (ctx2, tree2) <- sub ctx1 ty2' ty2''
      ret "SubArr" ctx2 [tree1, tree2]
    (_, TAll bnd) -> do
      -- it is always better to use SubAllR first
      (a, ty2') <- unbind bnd
      (ctx', tree) <- sub (TVarBnd a : ctx) ty1 ty2'
      let (_, _, ctx2) = break3 (\case TVarBnd a' -> a == a'; _ -> False) ctx'
      ret "SubAllR" ctx2 [tree]
    (TAll bnd, _) | not (isAll ty2) -> do
      -- of course ty2 is not forall
      (a, ty1') <- unbind bnd
      let ty1'' = subst a (ETVar a) ty1'
      (ctx', tree) <- sub (ETVarBnd a : Mark a : ctx) ty1'' ty2
      let (_, _, ctx2) = break3 (\case Mark a' -> a == a'; _ -> False) ctx'
      ret "SubAllL" ctx2 [tree]
    (ETVar a, _) | a `notElem` toListOf fv ty2 -> do
      (ctx', tree) <- instL ctx a ty2
      ret "SubInstL" ctx' [tree]
    (_, ETVar a) | a `notElem` toListOf fv ty1 -> do
      (ctx', tree) <- instR ctx ty1 a
      ret "SubInstR" ctx' [tree]
    _ -> throwError $ "No rule matching: " ++ showSubIn
  where
    showSubIn = show ctx ++ " |- " ++ show ty1 ++ " <: " ++ show ty2
    showSub ctx' = showSubIn ++ " -| " ++ show ctx'

    ret :: String -> Ctx -> [Tree String] -> InferMonad (Ctx, Tree String)
    ret rule ctx' tree = do
      lift $ tell ["Subtype[" ++ rule ++ "]: " ++ showSub ctx']
      return (ctx', Node (rule ++ ": " ++ showSub ctx') tree)

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
    showCheckIn = show ctx ++ " |- " ++ show tm ++ " <== " ++ show ty
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
      ret "InfLam" (TArr (ETVar a) (ETVar b)) ctx2 [tree]
    App tm1 tm2 -> do
      (ty1, ctx', tree1) <- infer ctx tm1
      ty1' <- appCtxTyp ctx' ty1
      (ty2, ctx'', tree2) <- inferApp ctx' ty1' tm2
      ret "InfApp" ty2 ctx'' [tree1, tree2]
    _ -> throwError $ "No rule matching: " ++ showInferIn
  where
    showInferIn = show ctx ++ " |- " ++ show tm
    showInfer ty' ctx' = showInferIn ++ " ==> " ++ show ty' ++ " -| " ++ show ctx'

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

runDK :: Trm -> Either String (Tree String)
runDK tm = case runInferMonad $ infer [] tm of
  Left errs -> Left (intercalate "\n" errs)
  Right ((_, _, tree), _) -> Right tree
