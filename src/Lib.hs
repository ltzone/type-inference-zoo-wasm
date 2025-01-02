{-# OPTIONS_GHC -fno-warn-orphans #-}

module Lib (InferMonad, runInferMonad, freshTVar, break3) where

import Control.Monad.RWS (MonadTrans (lift), RWST, get, put, runRWST)
import Control.Monad.Trans.Except (ExceptT (..), runExceptT)
import Syntax (TyVar)
import Unbound.Generics.LocallyNameless (FreshMT, runFreshMT)
import Unbound.Generics.LocallyNameless.Fresh (Fresh (..))
import Unbound.Generics.LocallyNameless.Name (s2n)

type InferMonad = ExceptT String (RWST () [String] Int (FreshMT Maybe))

instance (Monoid w, Fresh m) => Fresh (RWST r w s m) where
  fresh = lift . fresh

runInferMonad :: InferMonad a -> Either [String] (a, [String])
runInferMonad m = case runFreshMT $ runRWST (runExceptT m) () 0 of
  Nothing -> Left ["Computation failed"]
  Just (Left s, _, msgs) -> Left (s : msgs)
  Just (Right res, _, msgs) -> Right (res, msgs)

freshTVar :: InferMonad TyVar
freshTVar = do
  let letters = ["a", "b", "c", "d"]
  varId <- get
  put (varId + 1)
  fresh . s2n $ letters !! (varId `mod` length letters)

break3 :: (a -> Bool) -> [a] -> ([a], Maybe a, [a])
break3 p xs = case break p xs of
  (ys, []) -> (ys, Nothing, [])
  (ys, z : zs) -> (ys, Just z, zs)
