{-# LANGUAGE FlexibleInstances #-}

module Subtyping.Recursive.Translate (translation, runTranslationS, TranslationResult (..)) where

import Lib (Derivation (..), InferMonad, InferResult (..), freshTVar, freshLVar, runInferMonad)
import Syntax (Typ (..), TyVar)
import Unbound.Generics.LocallyNameless (subst, unbind, bind)
import Control.Monad.Except (throwError)

-- Data structure for translation results
data TranslationResult = TranslationResult
  { sourceType :: Typ,
    targetType :: Typ,
    translationDerivation :: [Derivation],
    translationErrorMsg :: Maybe String
  }


substp :: Bool -> TyVar -> Typ -> Typ -> InferMonad Typ
substp contra var replacement typ = case typ of
  TInt -> return TInt
  TBool -> return TBool
  TTop -> return TTop
  TBot -> return TBot
  TVar v | contra && (v == var) -> return replacement
         | otherwise -> return $ TVar v
  ETVar _ ->
    throwError "existential variables not supported in polarized substitution"
  STVar _ ->
    throwError "existential variables not supported in polarized substitution"
  TArr t1 t2 -> do
    t1' <- substp (not contra) var replacement t1
    t2' <- substp contra var replacement t2
    return $ TArr t1' t2'
  TIntersection t1 t2 -> do
    t1' <- substp contra var replacement t1
    t2' <- substp contra var replacement t2
    return $ TIntersection t1' t2'
  TUnion t1 t2 -> do
    t1' <- substp contra var replacement t1
    t2' <- substp contra var replacement t2
    return $ TUnion t1' t2'
  TAllB _ _ -> 
    throwError "bounded universal types not supported in polarized substitution"
  TTuple ts -> do
    ts' <- mapM (substp contra var replacement) ts
    return $ TTuple ts'
  TRecursive _ -> 
    throwError "Polarized substitution should not occur on recursive types directly"
  TLabel l t -> do
    t' <- substp contra var replacement t
    return $ TLabel l t'
  TLabeled l bnd -> do
    (v, t) <- unbind bnd
    t' <- substp contra var replacement t
    return $ TLabeled l (bind v t')
  TTranslatedMu bnd -> do
    ((v, l), t) <- unbind bnd
    t' <- substp contra var replacement t
    return $ TTranslatedMu (bind (v, l) t')
  
  
  

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
              expression = "\\texttt{Int} \\rightsquigarrow \\texttt{Int}"
          })
    TBool -> return
          ( TBool
          , Derivation {
              ruleId = "Trans-Bool",
              children = [],
              expression = "\\texttt{Bool} \\rightsquigarrow \\texttt{Bool}"
          })
    TVar name -> return
          ( TVar name
          , Derivation {
              ruleId = "Trans-Var",
              children = [],
              expression = show (TVar name) ++ " \\rightsquigarrow " ++ show (TVar name)
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
        rbody' <- substp False rvar (TLabeled l bodyTransClos) rbody
        let ty' = TTranslatedMu (bind (rvar, l) rbody')
        return
          ( ty'
          , Derivation {
              ruleId = "Trans-Mu",
              children = [d],
              expression = show ty ++ " \\rightsquigarrow " ++ show ty'
          })

    _ -> throwError $ "Translation not defined for type: " ++ show ty


-- Clean interface for running translation
runTranslationS :: Typ -> InferResult
runTranslationS tm = case runInferMonad (translation tm) of
  Left [] -> InferResult False Nothing [] (Just "Unknown error during translation") True
  Left (err : drvs) -> InferResult False Nothing (map (\drv -> Derivation "Debug" drv []) drvs) (Just err) True
  Right ((ty', drv), _) -> InferResult True (Just $ show ty') [drv] Nothing False
