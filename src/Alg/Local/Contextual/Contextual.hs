{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}

module Alg.Local.Contextual.Contextual (runContextual) where

import Control.Monad.Except (throwError)
import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Data.Data (Typeable)
import Data.Foldable (find)
import Data.Tree (Tree (Node))
import GHC.Generics (Generic)
import Lib (InferMonad, runInferMonad)
import Syntax (TmVar, Trm (..), Typ (..))
import Unbound.Generics.LocallyNameless (Alpha, aeq, unbind)

data EnvEntry
  = VarBnd TmVar Typ

type Env = [EnvEntry]

data Ctx = CEmpty | CTyp Typ | CConsTrm Trm Ctx
  deriving (Generic, Typeable)

instance Alpha Ctx

instance {-# OVERLAPPING #-} Show [EnvEntry] where
  show :: [EnvEntry] -> String
  show [] = ""
  show (VarBnd x ty : env) = show x ++ " : " ++ show ty ++ ", " ++ show env

instance Show Ctx where
  show :: Ctx -> String
  show CEmpty = "[]"
  show (CTyp ty) = show ty
  show (CConsTrm tm ctx) = "[" ++ show tm ++ "] |-> " ++ show ctx

genericConsumer :: Trm -> Bool
genericConsumer (LitInt _) = True
genericConsumer (LitBool _) = True
genericConsumer (Var _) = True
genericConsumer (Ann _ _) = True
genericConsumer _ = False

match :: Env -> Typ -> Ctx -> InferMonad (Tree String)
match env ty ctx = do
  lift $ tell ["Matching: " ++ showMatch]
  case (ty, ctx) of
    (_, CEmpty) -> ret "SubEmpty" []
    (_, CTyp ty') | aeq ty ty' -> ret "SubType" []
    (TArr ty1 ty2, CConsTrm tm ctx') -> do
      (_, tree1) <- infer env (CTyp ty1) tm
      tree2 <- match env ty2 ctx'
      ret "SubTerm" [tree1, tree2]
    (_, _) -> throwError $ "No rule matching: " ++ showMatch
  where
    showMatch = show env ++ " |- " ++ show ty ++ " ~ " ++ show ctx

    ret :: String -> [Tree String] -> InferMonad (Tree String)
    ret rule trees = do
      lift $ tell ["Matched[" ++ rule ++ "]: " ++ showMatch]
      return $ Node (rule ++ ": " ++ showMatch) trees

infer :: Env -> Ctx -> Trm -> InferMonad (Typ, Tree String)
infer env ctx tm = do
  lift $ tell ["Infering: " ++ showInferIn]
  case (ctx, tm) of
    (CEmpty, LitInt _) -> ret "ALitInt" TInt []
    (CEmpty, LitBool _) -> ret "ALitBool" TBool []
    (CEmpty, Var x)
      | Just (VarBnd _ ty) <- find (\case VarBnd x' _ -> x == x') env ->
          ret "AVar" ty []
    (CEmpty, Ann tm1 ty) -> do
      (_, tree) <- infer env (CTyp ty) tm1
      ret "AAnn" ty [tree]
    (_, App tm1 tm2) -> do
      (arrTy, tree) <- infer env (CConsTrm tm2 ctx) tm1
      case arrTy of
        TArr _ ty2 -> ret "AApp" ty2 [tree]
        _ -> throwError $ "Non-function type: " ++ show arrTy
    (CTyp (TArr ty1 ty2), Lam bnd) -> do
      (x, tm1) <- unbind bnd
      (ty3, tree) <- infer (VarBnd x ty1 : env) (CTyp ty2) tm1
      ret "ALam1" (TArr ty1 ty3) [tree]
    (CConsTrm tm2 ctx', Lam bnd) -> do
      (x, tm1) <- unbind bnd
      (ty1, tree1) <- infer env CEmpty tm2
      (ty2, tree2) <- infer (VarBnd x ty1 : env) ctx' tm1
      ret "ALam2" (TArr ty1 ty2) [tree1, tree2]
    (_, _) | not (aeq ctx CEmpty) && genericConsumer tm -> do
      (ty, tree1) <- infer env CEmpty tm
      tree2 <- match env ty ctx
      ret "ASub" ty [tree1, tree2]
    (_, _) -> throwError $ "No rule matching: " ++ showInferIn
  where
    showInferIn = show env ++ " |- " ++ show ctx ++ " => " ++ show tm

    showInfer :: Typ -> String
    showInfer ty = showInferIn ++ " : " ++ show ty

    ret :: String -> Typ -> [Tree String] -> InferMonad (Typ, Tree String)
    ret rule ty trees = do
      lift $ tell ["Infered[" ++ rule ++ "]: " ++ showInfer ty]
      return (ty, Node (rule ++ ": " ++ showInfer ty) trees)

runInfer :: Env -> Ctx -> Trm -> Either [String] ((Typ, Tree String), [String])
runInfer env ctx tm = runInferMonad $ infer env ctx tm

runContextual :: Trm -> Either String (Tree String)
runContextual tm = case runInfer [] CEmpty tm of
  Left errs -> Left (unlines errs)
  Right ((_, tree), _) -> Right tree
