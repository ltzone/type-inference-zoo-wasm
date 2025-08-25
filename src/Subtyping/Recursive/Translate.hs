{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Subtyping.Recursive.Translate (runTranslation, TranslationResult(..)) where


import Control.Monad.Except (MonadError (throwError))
import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Lib (Derivation (..), InferMonad, InferResult (..), freshTVar, freshLVar, runInferMonad, toJson)
import Syntax (Typ (..), TyVar)
import Unbound.Generics.LocallyNameless (subst, unbind, bind)
import Parser (parseTyp)
import GHC.Conc (TVar)

-- Data structure for translation results
data TranslationResult = TranslationResult
  { sourceType :: Typ
  , targetType :: Typ
  , translationDerivation :: [Derivation]
  , translationErrorMsg :: Maybe String
  }


-- substp :: Bool -> TyVar -> Typ -> Typ -> Typ
-- substp _ _ _ t = t


translation :: Typ -> InferMonad (Typ, Derivation)
translation ty = do
  case ty of
    TTop -> 
        return 
          ( TTop
          , Derivation {
              ruleId = "Trans-Top",
              children = [],
              expression = "\\top \\rightsquigarrow \\top"
          })
    TBot ->
        return 
          ( TBot
          , Derivation {
              ruleId = "Trans-Bot",
              children = [],
              expression = "\\bot \\rightsquigarrow \\bot"
          })
    TInt -> return
          ( TInt
          , Derivation {
              ruleId = "Trans-Int",
              children = [],
              expression = "\\text{int} \\rightsquigarrow \\text{int}"
          })
    TBool -> return
          ( TBool
          , Derivation {
              ruleId = "Trans-Bool",
              children = [],
              expression = "\\text{bool} \\rightsquigarrow \\text{bool}"
          })
    TVar name -> return
          ( TVar name
          , Derivation {
              ruleId = "Trans-Var",
              children = [],
              expression = show name ++ " \\rightsquigarrow " ++ show name
          })
    TArr ty1 ty2 -> do
        (ty1', d1) <- translation ty1
        (ty2', d2) <- translation ty2
        return
          ( TArr ty1' ty2'
          , Derivation {
              ruleId = "Trans-Fun",
              children = [d1, d2],
              expression = "(" ++ show ty ++ ") \\rightsquigarrow (" ++ show (TArr ty1' ty2') ++ ")"
          })

    TIntersection ty1 ty2 -> do
        (ty1', d1) <- translation ty1
        (ty2', d2) <- translation ty2
        return
          ( TIntersection ty1' ty2'
          , Derivation {
              ruleId = "Trans-And",
              children = [d1, d2],
              expression = "(" ++ show ty ++ ") \\rightsquigarrow (" ++ show (TIntersection ty1' ty2') ++ ")"
          })

    TRecursive body -> do
        (var, body') <- unbind body
        a <- freshTVar
        let bodyOpen = subst var (TVar a) body'
        (bodyTrans, d) <- translation bodyOpen
        let bodyTransClos = bind a bodyTrans
        (rvar, rbody) <- unbind bodyTransClos
        l <- freshLVar
        
        
        
        -- !!!!! TODO change this to polarized substitution
        let ty' = TTranslatedMu (subst rvar (TLabeled l bodyTransClos) rbody)
        return
          ( ty'
          , Derivation {
              ruleId = "Trans-Mu",
              children = [d],
              expression = show ty ++ " \\rightsquigarrow " ++ show ty'
          })

    _ -> throwError $ "Translation not defined for type: " ++ show ty
