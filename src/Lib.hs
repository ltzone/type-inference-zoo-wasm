module Lib (InferMonad, runInferMonad) where

import Control.Monad.Trans.Except (ExceptT (..), runExceptT)
import Control.Monad.Writer (WriterT (runWriterT))
import Unbound.Generics.LocallyNameless (FreshMT, runFreshMT)

type InferMonad = ExceptT String (WriterT [String] (FreshMT Maybe))

runInferMonad :: InferMonad a -> Either [String] (a, [String])
runInferMonad m = case runFreshMT $ runWriterT (runExceptT m) of
  Nothing -> Left ["Computation failed"]
  Just (Left s, msgs) -> Left (s : msgs)
  Just (Right res, msgs) -> Right (res, msgs)
