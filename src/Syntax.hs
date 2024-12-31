{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Syntax (TyVar, TmVar, Typ (..), PrimOp (..), opTyp, Trm (..)) where

import Data.Data (Typeable)
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless

type TyVar = Name Typ

type TmVar = Name Trm

data Typ
  = TInt
  | TBool
  | TVar TyVar
  | TArr Typ Typ
  | TAll (Bind TyVar Typ)
  | TTuple [Typ]
  deriving (Generic, Typeable)

data PrimOp
  = Add
  | Sub
  | Mul
  | Div
  deriving (Eq, Generic)

opTyp :: PrimOp -> Typ
opTyp Add = TArr TInt (TArr TInt TInt)
opTyp Sub = TArr TInt (TArr TInt TInt)
opTyp Mul = TArr TInt (TArr TInt TInt)
opTyp Div = TArr TInt (TArr TInt TInt)

data Trm
  = LitInt Integer
  | LitBool Bool
  | Var TmVar
  | Lam (Bind TmVar Trm)
  | App Trm Trm
  | Ann Trm Typ
  | Let Trm (Bind TmVar Trm)
  | LetRec (Bind TmVar (Trm, Trm))
  | Op PrimOp
  | BinOp PrimOp Trm Trm
  | If Trm Trm Trm
  | Tuple [Trm]
  deriving (Generic, Typeable)

instance Alpha Typ

instance Alpha Trm

instance Alpha PrimOp

instance Subst Trm Typ

instance Subst Trm PrimOp

instance Subst Typ Typ where
  isvar (TVar v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst Trm Trm where
  isvar (Var v) = Just (SubstName v)
  isvar _ = Nothing

instance Show Typ where
  showsPrec prec ty = runFreshM $ showsPrecFresh prec ty
    where
      showsPrecFresh :: Int -> Typ -> FreshM ShowS
      showsPrecFresh _ TInt = return $ showString "Int"
      showsPrecFresh _ TBool = return $ showString "Bool"
      showsPrecFresh _ (TVar x) = return $ shows x
      showsPrecFresh p (TArr a b) = do
        a' <- showsPrecFresh 1 a
        b' <- showsPrecFresh 0 b
        return $ showParen (p > 0) $ a' . showString " -> " . b'
      showsPrecFresh p (TAll bnd) = do
        (x, t) <- unbind bnd
        t' <- showsPrecFresh 0 t
        return $ showParen (p > 0) $ showString "∀" . shows x . showString ". " . t'
      showsPrecFresh _ (TTuple ts) = do
        ts' <- mapM (showsPrecFresh 0) ts
        return $ showString "(" . foldr1 (\a b -> a . showString ", " . b) ts' . showString ")"

showOp :: PrimOp -> ShowS
showOp Add = showString "+"
showOp Sub = showString "-"
showOp Mul = showString "*"
showOp Div = showString "/"

instance Show PrimOp where
  showsPrec _ = showParen True . showOp

instance Show Trm where
  showsPrec prec tm = runFreshM $ showsPrecFresh prec tm
    where
      showsPrecFresh :: Int -> Trm -> FreshM ShowS
      showsPrecFresh _ (LitInt i) = return $ shows i
      showsPrecFresh _ (LitBool b) = return $ shows b
      showsPrecFresh _ (Var x) = return $ shows x
      showsPrecFresh p (Lam bnd) = do
        (x, e) <- unbind bnd
        e' <- showsPrecFresh 0 e
        return $ showParen (p > 0) $ showString "λ" . shows x . showString ". " . e'
      showsPrecFresh p (App e1 e2) = do
        e1' <- showsPrecFresh 9 e1
        e2' <- showsPrecFresh 10 e2
        return $ showParen (p > 9) $ e1' . showString " " . e2'
      showsPrecFresh p (Ann e t) = do
        e' <- showsPrecFresh 1 e
        return $ showParen (p > 1) $ e' . showString " : " . shows t
      showsPrecFresh p (Let e1 bnd) = do
        (x, e2) <- unbind bnd
        e1' <- showsPrecFresh 0 e1
        e2' <- showsPrecFresh 0 e2
        return $ showParen (p > 0) $ showString "let " . shows x . showString " = " . e1' . showString " in " . e2'
      showsPrecFresh p (LetRec bnd) = do
        (x, (e1, e2)) <- unbind bnd
        e1' <- showsPrecFresh 0 e1
        e2' <- showsPrecFresh 0 e2
        return $ showParen (p > 0) $ showString "letrec " . shows x . showString " = " . e1' . showString " in " . e2'
      showsPrecFresh _ (Op op) = return $ shows op
      showsPrecFresh p (BinOp op e1 e2) | op `elem` [Add, Sub] = do
        e1' <- showsPrecFresh 6 e1
        e2' <- showsPrecFresh 7 e2
        return $ showParen (p > 6) $ e1' . showString " " . showOp op . showString " " . e2'
      showsPrecFresh p (BinOp op e1 e2) = do
        e1' <- showsPrecFresh 7 e1
        e2' <- showsPrecFresh 8 e2
        return $ showParen (p > 7) $ e1' . showString " " . showOp op . showString " " . e2'
      showsPrecFresh p (If e1 e2 e3) = do
        e1' <- showsPrecFresh 0 e1
        e2' <- showsPrecFresh 0 e2
        e3' <- showsPrecFresh 0 e3
        return $ showParen (p > 0) $ showString "if " . e1' . showString " then " . e2' . showString " else " . e3'
      showsPrecFresh _ (Tuple es) = do
        es' <- mapM (showsPrecFresh 0) es
        return $ showString "(" . foldr1 (\a b -> a . showString ", " . b) es' . showString ")"
