{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Alg.DK.Worklist.Common where

import Control.Monad.Error.Class (MonadError (throwError))
import Data.Data (Typeable)
import GHC.Generics (Generic)
import Lib (InferMonad, runInferMonad)
import Syntax (TmVar, Trm, TyVar, Typ)
import Unbound.Generics.LocallyNameless (Alpha, Bind, Subst, bind, fv, s2n, subst, unbind)
import Unbound.Generics.LocallyNameless.Fresh (FreshM, runFreshM)
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

data Judgment
  = Sub Typ Typ
  | Chk Trm Typ
  | Inf Trm (Bind TyVar Judgment)
  | InfApp Typ Trm (Bind TyVar Judgment)
  | InfTApp Typ Typ (Bind TyVar Judgment)
  | Match Typ (Bind TyVar Judgment)
  | End
  deriving (Generic, Typeable)

data TBind
  = TVarBind
  | ETVarBind
  | STVarBind
  | TVarBBind Typ
  | STVarBBind Typ
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

substWLOrdQuick :: [Entry] -> TyVar -> Typ -> Worklist -> InferMonad Worklist
substWLOrdQuick move a ty ws = case ws of
  [] -> throwError $ show a ++ "is not found"
  entry@(WTVar b ETVarBind) : ws'
    | a == b -> return $ move ++ ws'
    | b `notElem` toListOf fv ty -> do
        ws'' <- substWLOrdQuick move a ty ws'
        return $ entry : ws''
    | otherwise -> substWLOrdQuick (entry : move) a ty ws'
  WTVar b bnd : ws'
    | b `notElem` toListOf fv ty -> do
        ws'' <- substWLOrdQuick move a ty ws'
        return $ WTVar b (subst a ty bnd) : ws''
    | otherwise -> throwError $ show b ++ " occurs in " ++ show ty
  WVar x t : ws' -> do
    ws'' <- substWLOrdQuick move a ty ws'
    return $ WVar x (subst a ty t) : ws''
  WJug c : ws' -> do
    ws'' <- substWLOrdQuick move a ty ws'
    return $ WJug (subst a ty c) : ws''

substWLOrd :: TyVar -> Typ -> Worklist -> InferMonad Worklist
substWLOrd = substWLOrdQuick []

runInfer :: (String -> Worklist -> InferMonad a) -> Worklist -> Either [String] [String]
runInfer infer ws = case runInferMonad $ infer "Init" ws of
  Left errs -> Left errs
  Right (_, msgs) -> Right msgs

initWL :: Trm -> [Entry]
initWL tm = [WJug (Inf tm (bind (s2n "_") End))]

instance {-# OVERLAPPING #-} Show [Entry] where
  show [] = "⋅"
  show (WTVar a b : ws) =
    show ws
      ++ ", "
      ++ case b of
        TVarBind -> show a
        ETVarBind -> "^" ++ show a
        STVarBind -> "~" ++ show a
        TVarBBind t -> show a ++ " <: " ++ show t
        STVarBBind t -> "~" ++ show a ++ " <: " ++ show t
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
      showsPrecFresh _ (InfTApp t1 t2 bnd) = do
        (x, j) <- unbind bnd
        j' <- showsPrecFresh 0 j
        return $ shows t1 . showString " o " . shows t2 . showString " =>>" . shows x . showString " " . j'
      showsPrecFresh _ (Match t bnd) = do
        (x, j) <- unbind bnd
        j' <- showsPrecFresh 0 j
        return $ shows t . showString " |>" . shows x . showString " " . j'
      showsPrecFresh _ End = return $ showString "End"
