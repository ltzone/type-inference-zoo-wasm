{-# OPTIONS_GHC -fno-warn-orphans #-}

module Lib (InferMonad, runInferMonad, freshTVar, freshLVar, break3, Derivation (..), InferResult (..), toJson) where

import Control.Monad.RWS (MonadTrans (lift), RWST, get, put, runRWST)
import Control.Monad.Trans.Except (ExceptT (..), runExceptT)
import Data.Aeson (ToJSON(..), encode, object, (.=))
import qualified Data.Aeson.Key as Key
import qualified Data.ByteString.Lazy.Char8 as L8
import GHC.Generics ()
import Syntax (TyVar, LabelVar)
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


freshLVar :: InferMonad LabelVar
freshLVar = do
  let letters = ["l"]
  varId <- get
  put (varId + 1)
  fresh . s2n $ letters !! (varId `mod` length letters)



break3 :: (a -> Bool) -> [a] -> ([a], Maybe a, [a])
break3 p xs = case break p xs of
  (ys, []) -> (ys, Nothing, [])
  (ys, z : zs) -> (ys, Just z, zs)

data Derivation = Derivation
  { ruleId :: String
  , expression :: String
  , children :: [Derivation]
  }

data InferResult = InferResult
  { success :: Bool
  , finalType :: Maybe String
  , derivation :: [Derivation]
  , errorMsg :: Maybe String
  , errorLatex :: Bool
  }

instance ToJSON Derivation where
  toJSON step = object
    [ Key.fromString "ruleId" .= ruleId step  
    , Key.fromString "expression" .= expression step
    , Key.fromString "children" .= children step
    ]

instance ToJSON InferResult where
  toJSON result = object
    [ Key.fromString "success" .= success result
    , Key.fromString "finalType" .= finalType result
    , Key.fromString "derivation" .= derivation result
    , Key.fromString "error" .= errorMsg result
    , Key.fromString "errorLatex" .= errorLatex result
    ]

toJson :: InferResult -> String
toJson = L8.unpack . encode
