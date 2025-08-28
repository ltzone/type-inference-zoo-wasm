{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}

module Typing.Local.Contextual.Contextual (runContextual, contextualMeta) where

import Control.Monad.Except (throwError)
import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Data.Data (Typeable)
import Data.Foldable (find)
import Data.List (intercalate)
import GHC.Generics (Generic)
import Lib (Derivation (..), InferMonad, InferResult (..), runInferMonad, AlgMeta (..), Paper (..), Rule (..), RuleGroup (..), Variant (..))
import Syntax (TmVar, Trm (..), Typ (..), latexifyVar)
import Unbound.Generics.LocallyNameless (Alpha, aeq, unbind)

data EnvEntry
  = VarBnd TmVar Typ

type Env = [EnvEntry]

data Ctx = CEmpty | CTyp Typ | CConsTrm Trm Ctx
  deriving (Generic, Typeable)

instance Alpha Ctx

instance Show EnvEntry where
  show :: EnvEntry -> String
  show (VarBnd x ty) = latexifyVar x ++ ": " ++ show ty

instance {-# OVERLAPPING #-} Show [EnvEntry] where
  show :: [EnvEntry] -> String
  show = intercalate ", " . map show . reverse

instance Show Ctx where
  show :: Ctx -> String
  show CEmpty = "\\square"
  show (CTyp ty) = show ty
  show (CConsTrm tm ctx) = "\\boxed{" ++ show tm ++ "} \\leadsto " ++ show ctx

genericConsumer :: Trm -> Bool
genericConsumer (LitInt _) = True
genericConsumer (LitBool _) = True
genericConsumer (Var _) = True
genericConsumer (Ann _ _) = True
genericConsumer _ = False

match :: Env -> Typ -> Ctx -> InferMonad Derivation
match env ty ctx = do
  lift $ tell ["\\text{Matching: } " ++ showMatch]
  case (ty, ctx) of
    (_, CEmpty) -> ret "SubEmpty" []
    (_, CTyp ty') | aeq ty ty' -> ret "SubType" []
    (TArr ty1 ty2, CConsTrm tm ctx') -> do
      (_, drv1) <- infer env (CTyp ty1) tm
      drv2 <- match env ty2 ctx'
      ret "SubTerm" [drv1, drv2]
    (_, _) -> throwError $ "\\text{No rule matching: } " ++ showMatch
  where
    showMatch = show env ++ " \\vdash " ++ show ty ++ " \\sim " ++ show ctx

    ret :: String -> [Derivation] -> InferMonad Derivation
    ret rule drvs = do
      lift $ tell ["\\text{Matched[" ++ rule ++ "]: } " ++ showMatch]
      return $ Derivation rule showMatch drvs

infer :: Env -> Ctx -> Trm -> InferMonad (Typ, Derivation)
infer env ctx tm = do
  lift $ tell ["\\text{Inferring: } " ++ showInferIn]
  case (ctx, tm) of
    (CEmpty, LitInt _) -> ret "ALitInt" TInt []
    (CEmpty, LitBool _) -> ret "ALitBool" TBool []
    (CEmpty, Var x)
      | Just (VarBnd _ ty) <- find (\case VarBnd x' _ -> x == x') env ->
          ret "AVar" ty []
    (CEmpty, Ann tm1 ty) -> do
      (_, drv) <- infer env (CTyp ty) tm1
      ret "AAnn" ty [drv]
    (_, App tm1 tm2) -> do
      (arrTy, drv) <- infer env (CConsTrm tm2 ctx) tm1
      case arrTy of
        TArr _ ty2 -> ret "AApp" ty2 [drv]
        _ -> throwError $ "\\text{Non-function type: } " ++ show arrTy
    (CTyp (TArr ty1 ty2), Lam bnd) -> do
      (x, tm1) <- unbind bnd
      (ty3, drv) <- infer (VarBnd x ty1 : env) (CTyp ty2) tm1
      ret "ALam1" (TArr ty1 ty3) [drv]
    (CConsTrm tm2 ctx', Lam bnd) -> do
      (x, tm1) <- unbind bnd
      (ty1, drv1) <- infer env CEmpty tm2
      (ty2, drv2) <- infer (VarBnd x ty1 : env) ctx' tm1
      ret "ALam2" (TArr ty1 ty2) [drv1, drv2]
    (_, _) | not (aeq ctx CEmpty) && genericConsumer tm -> do
      (ty, drv1) <- infer env CEmpty tm
      drv2 <- match env ty ctx
      ret "ASub" ty [drv1, drv2]
    (_, _) -> throwError $ "\\text{No rule matching: } " ++ showInferIn
  where
    showInferIn = show env ++ " \\vdash " ++ show ctx ++ " \\Rightarrow " ++ show tm

    showInfer :: Typ -> String
    showInfer ty = showInferIn ++ " \\Rightarrow " ++ show ty

    ret :: String -> Typ -> [Derivation] -> InferMonad (Typ, Derivation)
    ret rule ty drvs = do
      lift $ tell ["\\text{Inferred[" ++ rule ++ "]: } " ++ showInfer ty]
      return (ty, Derivation rule (showInfer ty) drvs)

runInfer :: Env -> Ctx -> Trm -> Either [String] ((Typ, Derivation), [String])
runInfer env ctx tm = runInferMonad $ infer env ctx tm

runContextual :: Trm -> InferResult
runContextual tm = case runInfer [] CEmpty tm of
  Left [] -> InferResult False Nothing [] (Just "\\text{Unknown error}") True
  Left (err : drvs) -> InferResult False Nothing (map (\drv -> Derivation "Debug" drv []) drvs) (Just err) True
  Right ((ty, drv), _) -> InferResult True (Just $ show ty) [drv] Nothing False

contextualMeta :: AlgMeta
contextualMeta = AlgMeta
  { metaId = "Contextual"
  , metaName = "Contextual Typing"
  , metaLabels = ["Local", "Contextual"]
  , metaViewMode = "tree"
  , metaMode = "inference"
  , metaPaper = Paper
    { paperTitle = "Contextual Typing"
    , paperAuthors = ["Xu Xue", "Bruno C. d. S. Oliveira"]
    , paperYear = 2024
    , paperUrl = "https://dl.acm.org/doi/10.1145/3674655"
    }
  , metaVariants = Just
    [ Variant "base" "Base" "Basic contextual typing algorithm"
    , Variant "extension" "Extension" "Extended contextual typing with additional features"
    ]
  , metaDefaultVariant = Just "base"
  , metaRules = []
  , metaRuleGroups = Just
    [ RuleGroup
      { groupId = "typing"
      , groupName = "Typing"
      , groupDescription = Just "Under environment $\\Gamma$, expression $e$ has type $\\tau$"
      , groupFormula = Just "\\boxed{\\Gamma \\vdash e : \\tau}"
      , groupRules = 
        [ Rule "CTVar" "CTVar" ["x : \\sigma \\in \\Gamma"] "\\Gamma \\vdash x : \\sigma" Nothing Nothing
        , Rule "CTApp" "CTApp" ["\\Gamma \\vdash e_1 : \\tau_1 \\to \\tau_2", "\\Gamma \\vdash e_2 : \\tau_1"] "\\Gamma \\vdash e_1~e_2 : \\tau_2" Nothing Nothing
        , Rule "CTAbs" "CTAbs" ["\\Gamma, x : \\tau_1 \\vdash e : \\tau_2"] "\\Gamma \\vdash \\lambda x.~e : \\tau_1 \\to \\tau_2" Nothing Nothing
        ]
      }
    , RuleGroup
      { groupId = "matching"
      , groupName = "Matching"
      , groupDescription = Just "Type matching produces substitution $S$ from types $\\tau_1$ and $\\tau_2$"
      , groupFormula = Just "\\boxed{\\tau_1 \\triangleleft \\tau_2 \\Rightarrow S}"
      , groupRules = 
        [ Rule "MTVar" "MTVar" ["\\alpha \\text{ fresh}"] "\\alpha \\triangleleft \\tau \\Rightarrow [\\alpha \\mapsto \\tau]" Nothing Nothing
        , Rule "MTArr" "MTArr" ["\\tau_1 \\triangleleft \\tau_3 \\Rightarrow S_1", "S_1(\\tau_2) \\triangleleft S_1(\\tau_4) \\Rightarrow S_2"] "\\tau_1 \\to \\tau_2 \\triangleleft \\tau_3 \\to \\tau_4 \\Rightarrow S_2 \\circ S_1" Nothing Nothing
        ]
      }
    ]
  , metaVariantRules = Just
    [ ("base", 
      [ RuleGroup
        { groupId = "typing"
        , groupName = "Typing"
        , groupDescription = Just "Under environment $\\Gamma$, expression $e$ has type $\\tau$"
        , groupFormula = Just "\\boxed{\\Gamma \\vdash e : \\tau}"
        , groupRules = 
          [ Rule "CTVar" "CTVar" ["x : \\sigma \\in \\Gamma"] "\\Gamma \\vdash x : \\sigma" Nothing Nothing
          , Rule "CTApp" "CTApp" ["\\Gamma \\vdash e_1 : \\tau_1 \\to \\tau_2", "\\Gamma \\vdash e_2 : \\tau_1"] "\\Gamma \\vdash e_1~e_2 : \\tau_2" Nothing Nothing
          , Rule "CTAbs" "CTAbs" ["\\Gamma, x : \\tau_1 \\vdash e : \\tau_2"] "\\Gamma \\vdash \\lambda x.~e : \\tau_1 \\to \\tau_2" Nothing Nothing
          ]
        }
      ])
    , ("extension",
      [ RuleGroup
        { groupId = "typing"
        , groupName = "Typing"
        , groupDescription = Just "Under environment $\\Gamma$, expression $e$ has type $\\tau$"
        , groupFormula = Just "\\boxed{\\Gamma \\vdash e : \\tau}"
        , groupRules = 
          [ Rule "CTVar" "CTVar" ["x : \\sigma \\in \\sigma"] "\\Gamma \\vdash x : \\sigma" Nothing Nothing
          , Rule "CTApp" "CTApp" ["\\Gamma \\vdash e_1 : \\tau_1 \\to \\tau_2", "\\Gamma \\vdash e_2 : \\tau_1"] "\\Gamma \\vdash e_1~e_2 : \\tau_2" Nothing Nothing
          , Rule "CTAbs" "CTAbs" ["\\Gamma, x : \\tau_1 \\vdash e : \\tau_2"] "\\Gamma \\vdash \\lambda x.~e : \\tau_1 \\to \\tau_2" Nothing Nothing
          , Rule "CTLet" "CTLet" ["\\Gamma \\vdash e_1 : \\tau_1", "\\Gamma, x : \\tau_1 \\vdash e_2 : \\tau_2"] "\\Gamma \\vdash \\text{let } x = e_1 \\text{ in } e_2 : \\tau_2" Nothing Nothing
          ]
        }
      , RuleGroup
        { groupId = "matching"
        , groupName = "Matching"
        , groupDescription = Just "Type matching produces substitution $S$ from types $\\tau_1$ and $\\tau_2$"
        , groupFormula = Just "\\boxed{\\tau_1 \\triangleleft \\tau_2 \\Rightarrow S}"
        , groupRules = 
          [ Rule "MTVar" "MTVar" ["\\alpha \\text{ fresh}"] "\\alpha \\triangleleft \\tau \\Rightarrow [\\alpha \\mapsto \\tau]" Nothing Nothing
          , Rule "MTArr" "MTArr" ["\\tau_1 \\triangleleft \\tau_3 \\Rightarrow S_1", "S_1(\\tau_2) \\triangleleft S_1(\\tau_4) \\Rightarrow S_2"] "\\tau_1 \\to \\tau_2 \\triangleleft \\tau_3 \\to \\tau_4 \\Rightarrow S_2 \\circ S_1" Nothing Nothing
          , Rule "MTUnit" "MTUnit" [] "\\text{unit} \\triangleleft \\text{unit} \\Rightarrow \\text{id}" Nothing Nothing
          ]
        }
      , RuleGroup
        { groupId = "inference"
        , groupName = "Inference"
        , groupDescription = Just "Type inference for expressions without explicit type annotations"
        , groupFormula = Just "\\boxed{\\Gamma \\vdash e \\Rightarrow \\tau}"
        , groupRules = 
          [ Rule "InfVar" "InfVar" ["x : \\sigma \\in \\Gamma"] "\\Gamma \\vdash x \\Rightarrow \\sigma" Nothing Nothing
          , Rule "InfApp" "InfApp" ["\\Gamma \\vdash e_1 \\Rightarrow \\tau_1 \\to \\tau_2", "\\Gamma \\vdash e_2 \\Leftarrow \\tau_1"] "\\Gamma \\vdash e_1~e_2 \\Rightarrow \\tau_2" Nothing Nothing
          ]
        }
      ])
    ]
  }
