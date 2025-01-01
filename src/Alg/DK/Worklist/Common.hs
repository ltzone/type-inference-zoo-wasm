{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Alg.DK.Worklist.Common where

import Control.Monad.Error.Class (MonadError (throwError))
import Data.Data (Typeable)
import GHC.Generics (Generic)
import Lib (InferMonad)
import Syntax
import Unbound.Generics.LocallyNameless (Alpha, Bind, Subst, subst, unbind)
import Unbound.Generics.LocallyNameless.Fresh

data Judgment
  = Sub Typ Typ
  | Chk Trm Typ
  | Inf Trm (Bind TyVar Judgment)
  | InfApp Typ Trm (Bind TyVar Judgment)
  | End
  deriving (Generic, Typeable)

data TBind
  = TVarBind
  | ETVarBind
  | STVarBind
  deriving (Generic, Typeable, Show)

data Entry
  = WTVar TyVar TBind
  | WVar TmVar Typ
  | WJug Judgment
  deriving (Generic, Typeable, Show)

type Worklist = [Entry]

instance Alpha Judgment

instance Alpha TBind

instance Alpha Entry

instance Subst Typ Judgment

instance Subst Typ TBind

instance Subst Typ Entry

substWL :: TyVar -> Typ -> [Entry] -> Worklist -> InferMonad Worklist
substWL a ty entries ws = case ws of
  [] -> throwError $ show a ++ "is not found"
  WTVar a' _ : ws' | a == a' -> return $ entries ++ ws'
  WTVar a' b : ws' -> do
    ws'' <- substWL a ty entries ws'
    return $ WTVar a' (subst a ty b) : ws''
  WVar x t : ws' -> do
    ws'' <- substWL a ty entries ws'
    return $ WVar x (subst a ty t) : ws''
  WJug c : ws' -> do
    ws'' <- substWL a ty entries ws'
    return $ WJug (subst a ty c) : ws''

before :: Worklist -> TyVar -> TyVar -> Bool
before ws a b =
  let (ws1, _) = break (\case WTVar a' _ -> a == a'; _ -> False) ws
      (ws1', _) = break (\case WTVar b' _ -> b == b'; _ -> False) ws
   in length ws1 > length ws1'

instance {-# OVERLAPPING #-} Show [Entry] where
  show [] = "⋅"
  show (WTVar a b : ws) =
    show ws
      ++ ", "
      ++ case b of
        TVarBind -> ""
        ETVarBind -> "^"
        STVarBind -> "~"
      ++ show a
  show (WVar x t : ws) = show ws ++ ", " ++ show x ++ ": " ++ show t
  show (WJug c : ws) = show ws ++ " ||- " ++ show c

instance Show Judgment where
  showsPrec prec jug = runFreshM $ showsPrecFresh prec jug
    where
      showsPrecFresh :: Int -> Judgment -> FreshM ShowS
      showsPrecFresh _ (Sub t1 t2) = return $ shows t1 . showString " <: " . shows t2
      showsPrecFresh _ (Chk e t) = return $ shows e . showString " <== " . shows t
      showsPrecFresh _ (Inf e bnd) = do
        (x, j) <- unbind bnd
        j' <- showsPrecFresh 0 j
        return $ shows e . showString " ==>" . shows x . showString " " . j'
      showsPrecFresh _ (InfApp t e bnd) = do
        (x, j) <- unbind bnd
        j' <- showsPrecFresh 0 j
        return $ shows t . showString " * " . shows e . showString " =>>" . shows x . showString " " . j'
      showsPrecFresh _ End = return $ showString "End"
