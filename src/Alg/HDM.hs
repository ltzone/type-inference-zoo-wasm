module Alg.HDM (runHDM) where

import Control.Monad.Except
import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Data.List (intercalate)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Tree (Tree (Node))
import Lib (InferMonad, runInferMonad)
import Syntax (TmVar, Trm (..), TyVar, Typ (..))
import Unbound.Generics.LocallyNameless hiding (Subst)
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

type Env = Map.Map TmVar Typ

type Subst = Map.Map TyVar Typ

remove :: Env -> TmVar -> Env
remove env x = Map.delete x env

apply :: Subst -> Typ -> Typ
apply = substs . Map.toList

nullSubst :: Subst
nullSubst = Map.empty

compSubst :: Subst -> Subst -> Subst
compSubst s1 s2 = Map.map (apply s1) s2 `Map.union` s1

inst :: Typ -> InferMonad Typ
inst (TAll bnd) = do
  (_, t) <- unbind bnd
  inst t
inst t = return t

gen :: Env -> Typ -> Typ
gen env t = foldl (\t' x -> TAll $ bind x t') t ftv
  where
    tFtv = Set.fromList $ toListOf fv t
    envFtv = Set.fromList $ concatMap (toListOf fv) $ Map.elems env
    ftv = Set.toList $ tFtv `Set.difference` envFtv

mgu :: Typ -> Typ -> InferMonad Subst
mgu TInt TInt = return nullSubst
mgu TBool TBool = return nullSubst
mgu (TArr t1 t2) (TArr t1' t2') = do
  s1 <- mgu t1 t1'
  s2 <- mgu (apply s1 t2) (apply s1 t2')
  return (s1 `compSubst` s2)
mgu (TVar a) t = varBind a t
mgu t (TVar a) = varBind a t
mgu t1 t2 = throwError $ "cannot unify " ++ show t1 ++ " with " ++ show t2

varBind :: TyVar -> Typ -> InferMonad Subst
varBind u t
  | aeq t (TVar u) = return nullSubst
  | u `elem` toListOf fv t = throwError $ show u ++ " occurs in " ++ show t
  | otherwise = return $ Map.singleton u t

freshTVar :: InferMonad TyVar
freshTVar = fresh . s2n $ "a"

infer :: Env -> Trm -> InferMonad (Subst, Typ, Tree String)
infer env tm = do
  lift $ tell ["Infering: " ++ showInput]
  case tm of
    LitInt _ -> ret "LitInt" nullSubst TInt []
    LitBool _ -> ret "LitBool" nullSubst TBool []
    Var x -> case Map.lookup x env of
      Nothing -> throwError $ "unbound variable " ++ show x
      Just poly -> do
        mono <- inst poly
        ret "Var" nullSubst mono []
    Lam bnd -> do
      (x, tm') <- unbind bnd
      a <- freshTVar
      let env' = env `Map.union` Map.singleton x (TVar a)
      (s1, t1, tree) <- infer env' tm'
      ret "Lam" s1 (TArr (apply s1 (TVar a)) t1) [tree]
    App tm1 tm2 -> do
      a <- freshTVar
      (s1, ty1, tree1) <- infer env tm1
      (s2, ty2, tree2) <- infer (Map.map (apply s1) env) tm2
      s3 <- mgu (apply s2 ty1) (TArr ty2 (TVar a))
      ret "App" (s3 `compSubst` s2 `compSubst` s1) (apply s3 (TVar a)) [tree1, tree2]
    Let tm1 bnd -> do
      (x, tm2) <- unbind bnd
      (s1, ty1, tree1) <- infer env tm1
      let t' = gen (Map.map (apply s1) env) ty1
          env' = Map.insert x t' env
      (s2, ty2, tree2) <- infer (Map.map (apply s1) env') tm2
      ret "Let" (s1 `compSubst` s2) ty2 [tree1, tree2]
    _ -> throwError "not implemented"
  where
    showInput :: String
    showInput = showEnv env ++ " |- " ++ show tm

    showOutput :: Subst -> Typ -> String
    showOutput s ty = showInput ++ " : " ++ show ty ++ " with " ++ showSubst s

    ret :: String -> Subst -> Typ -> [Tree String] -> InferMonad (Subst, Typ, Tree String)
    ret rule s ty trees = do
      lift $ tell ["Infered[" ++ rule ++ "]: " ++ showOutput s ty]
      return (s, ty, Node (rule ++ ": " ++ showOutput s ty) trees)

runHDM :: Trm -> Either String (Tree String)
runHDM tm = case runInferMonad $ infer Map.empty tm of
  Left errs -> Left (intercalate "\n" errs)
  Right ((_, _, tree), _) -> Right tree

showEnv :: Env -> String
showEnv env = intercalate ", " $ map (\(x, t) -> show x ++ ": " ++ show t) (Map.toList env)

showSubst :: Subst -> String
showSubst s = "{" ++ intercalate ", " (map (\(a, t) -> show t ++ " / " ++ show a) (Map.toList s)) ++ "}"
