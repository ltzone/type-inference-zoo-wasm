{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

-- TODO: need more test

module Alg.DK.Worklist.IU (runIU) where

import Alg.DK.Worklist.Common (Entry (..), Judgment (..), TBind (..), Worklist, initWL, substWLOrd)
import Control.Monad (msum, mzero)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.Logic (LogicT, observeT)
import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell))
import Data.Foldable (find)
import Lib (InferMonad, freshTVar, runInferMonad)
import Syntax (Trm (..), Typ (..), pattern TAll, pattern TLam)
import Unbound.Generics.LocallyNameless
  ( Fresh (fresh),
    Subst (subst),
    bind,
    fv,
    substBind,
    unbind,
  )
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

notAll :: Typ -> Bool
-- TODO: we should be careful about the wildcard when extending more types
notAll TInt = True
notAll TBool = True
notAll TTop = True
notAll TBot = False
notAll (TArr _ _) = True
notAll (TVar _) = True
notAll (ETVar _) = True
notAll (STVar _) = False
notAll (TAll _) = False
notAll (TIntersection ty1 ty2) = notAll ty1 && notAll ty2
notAll (TUnion ty1 ty2) = notAll ty1 || notAll ty2
notAll _ = False

mono :: Typ -> Bool
mono TInt = True
mono TBool = True
mono TTop = False
mono TBot = False
mono (TArr ty1 ty2) = mono ty1 && mono ty2
mono (TVar _) = True
mono (ETVar _) = True
mono (STVar _) = False
mono (TAll _) = False
mono (TIntersection _ _) = False
mono (TUnion _ _) = False
mono _ = False

infer :: Worklist -> LogicT InferMonad [(String, Worklist)]
infer ws = do
  lift $ tell [show ws]
  case ws of
    [] -> ret "empty" []
    WTVar _ _ : ws' -> retInf "GCTVar" ws'
    WVar _ _ : ws' -> retInf "GCVar" ws'
    WJug (Sub TInt TInt) : ws' -> retInf "SubReflInt" ws'
    WJug (Sub TBool TBool) : ws' -> retInf "SubReflBool" ws'
    WJug (Sub (TVar a) (TVar b)) : ws' | a == b -> retInf "SubReflTVar" ws'
    WJug (Sub (ETVar a) (ETVar b)) : ws' | a == b -> retInf "SubReflETVar" ws'
    WJug (Sub (STVar a) (STVar b)) : ws' | a == b -> retInf "SubReflSTVar" ws'
    WJug (Sub _ TTop) : ws' -> retInf "SubTop" ws'
    WJug (Sub TBot _) : ws' -> retInf "SubBot" ws'
    WJug (Sub (TArr ty1 ty2) (TArr ty1' ty2')) : ws' ->
      retInf "SubArr" $ WJug (Sub ty1' ty1) : WJug (Sub ty2 ty2') : ws'
    WJug (Sub (TAll bnd1) (TAll bnd2)) : ws' -> do
      a <- lift freshTVar
      let ty1 = substBind bnd1 (ETVar a)
          ty2 = substBind bnd2 (ETVar a)
      retInf "SubAll" $ WJug (Sub ty1 ty2) : WTVar a STVarBind : ws'
    WJug (Sub (ETVar a) ty) : ws'
      | a `notElem` toListOf fv ty,
        mono ty -> do
          ws'' <- lift $ substWLOrd a ty ws'
          retInf "SubInstETVar" ws''
    WJug (Sub ty (ETVar a)) : ws'
      | a `notElem` toListOf fv ty,
        mono ty -> do
          ws'' <- lift $ substWLOrd a ty ws'
          retInf "SubInstETVar" ws''
    WJug (Sub (ETVar a) ty@(TArr ty1 ty2)) : ws'
      | a `notElem` toListOf fv ty,
        not $ mono ty -> do
          a1 <- lift $ fresh a
          a2 <- lift $ fresh a
          ws'' <-
            lift $
              substWLOrd a (TArr (ETVar a1) (ETVar a2)) $
                WTVar a1 ETVarBind : WTVar a2 ETVarBind : ws'
          retInf "SubSplitL" $ WJug (Sub (TArr (ETVar a1) (ETVar a2)) (TArr ty1 ty2)) : ws''
    WJug (Sub ty@(TArr ty1 ty2) (ETVar a)) : ws'
      | a `notElem` toListOf fv ty,
        not $ mono ty -> do
          a1 <- lift $ fresh a
          a2 <- lift $ fresh a
          ws'' <-
            lift $
              substWLOrd a (TArr (ETVar a1) (ETVar a2)) $
                WTVar a1 ETVarBind : WTVar a2 ETVarBind : ws'
          retInf "SubSplitR" $ WJug (Sub (TArr ty1 ty2) (TArr (ETVar a1) (ETVar a2))) : ws''
    WJug (Sub _ _) : _ ->
      -- possibly overlapped rules; may need back-tracking
      msum
        [ ruleSubAllL,
          ruleSubIntersectionL,
          ruleSubIntersectionR,
          ruleSubIntersection,
          ruleSubUnionL,
          ruleSubUnionR,
          ruleSubUnion
        ]
    WJug End : ws' -> retInf "End" ws'
    WJug (Chk (Lam bnd) TTop) : ws' -> do
      (x, e) <- lift $ unbind bnd
      retInf "ChkLamTop" $ WJug (Chk e TTop) : WVar x TBot : ws'
    WJug (Chk (Lam bnd) (TArr ty1 ty2)) : ws' -> do
      (x, e) <- lift $ unbind bnd
      retInf "ChkLam" $ WJug (Chk e ty2) : WVar x ty1 : ws'
    entry@(WJug (Chk (Lam bnd) (ETVar a))) : ws' -> do
      (x, e) <- lift $ unbind bnd
      a1 <- lift $ fresh a
      a2 <- lift $ fresh a
      ws'' <-
        lift $
          substWLOrd a (TArr (ETVar a1) (ETVar a2)) $
            entry : WJug (Chk e (ETVar a2)) : WVar x (ETVar a1) : ws'
      retInf "ChkLamSplit" ws''
    WJug (Chk _ _) : _ ->
      -- possibly overlapped rules; may need back-tracking
      msum
        [ ruleChkIntersection,
          ruleChkUnionL,
          ruleChkUnionR,
          ruleChkSub
        ]
    WJug (Inf (Var x) j) : ws' -> do
      case find (\case WVar x' _ -> x == x'; _ -> False) ws' of
        Just (WVar _ ty) -> retInf "InfVar" $ WJug (substBind j ty) : ws'
        _ -> throwError $ show x ++ " is not found"
    WJug (Inf (Ann tm ty) j) : ws' ->
      retInf "InfAnn" $ WJug (Chk tm ty) : WJug (substBind j ty) : ws'
    WJug (Inf (TLam bnd) j) : ws' -> do
      (a, tm) <- lift $ unbind bnd
      case tm of -- to make my life easier
        Ann tm' ty ->
          retInf "InfTLam" $
            WJug (Chk tm' ty)
              : WTVar a TVarBind
              : WJug (substBind j (TAll (bind a ty)))
              : ws'
        _ -> throwError $ show tm ++ " is not an annotated term"
    WJug (Inf (LitInt _) j) : ws' ->
      retInf "InfLitInt" $ WJug (substBind j TInt) : ws'
    WJug (Inf (LitBool _) j) : ws' ->
      retInf "InfLitBool" $ WJug (substBind j TBool) : ws'
    WJug (Inf (App tm1 tm2) j) : ws' -> do
      a <- lift freshTVar
      b <- lift freshTVar
      let j' = Inf tm1 $ bind a $ Match (TVar a) $ bind b $ InfApp (TVar b) tm2 j
      retInf "InfApp" $ WJug j' : ws'
    WJug (Inf (TApp tm ty) j) : ws' -> do
      a <- lift freshTVar
      retInf "InfTApp" $ WJug (Inf tm (bind a (InfTApp (TVar a) ty j))) : ws'
    WJug (Inf (Lam bnd) j) : ws' -> do
      a <- lift freshTVar
      b <- lift freshTVar
      (x, e) <- lift $ unbind bnd
      retInf "InfLam" $
        WJug (Chk e (ETVar b))
          : WVar x (ETVar a)
          : WJug (substBind j (TArr (ETVar a) (ETVar b)))
          : WTVar a ETVarBind
          : WTVar b ETVarBind
          : ws'
    WJug (Match ty@(TArr _ _) j) : ws' ->
      retInf "MatchArr" $ WJug (substBind j ty) : ws'
    WJug (Match TBot j) : ws' ->
      retInf "MatchBot" $ WJug (substBind j (TArr TBot TBot)) : ws'
    WJug (Match (TAll bnd) j) : ws' -> do
      (a, ty) <- lift $ unbind bnd
      let j' = Match (subst a (ETVar a) ty) j
      retInf "MatchAll" $ WJug j' : WTVar a ETVarBind : ws'
    entry@(WJug (Match (ETVar a) _)) : ws' -> do
      a1 <- lift $ fresh a
      a2 <- lift $ fresh a
      ws'' <-
        lift $
          substWLOrd a (TArr (ETVar a1) (ETVar a2)) $
            entry : WTVar a1 ETVarBind : WTVar a2 ETVarBind : ws'
      retInf "MatchETVar" ws''
    WJug (Match (TUnion ty1 ty2) j) : ws' -> do
      a <- lift freshTVar
      b <- lift freshTVar
      let j' = Match ty1 $ bind a $ Match ty2 $ bind b $ MatchUnion (TVar a) (TVar b) j
      retInf "MatchUnion" $ WJug j' : ws'
    WJug (Match (TIntersection _ _) _) : _ ->
      msum
        [ ruleMatchIntersectionL,
          ruleMatchIntersectionR
        ]
    WJug (MatchUnion (TArr ty1 ty1') (TArr ty2 ty2') j) : ws' ->
      retInf "MatchUnionArr" $
        WJug (substBind j (TArr (TIntersection ty1 ty2) (TUnion ty1' ty2'))) : ws'
    WJug (InfApp (TArr ty1 ty2) tm j) : ws' ->
      retInf "InfApp" $ WJug (Chk tm ty1) : WJug (substBind j ty2) : ws'
    WJug (InfTApp (TAll bnd) ty2 j) : ws' ->
      retInf "InfTAppAll" $ WJug (substBind j (substBind bnd ty2)) : ws'
    WJug (InfTApp TBot _ j) : ws' ->
      retInf "InfTAppBot" $ WJug (substBind j TBot) : ws'
    WJug (InfTApp (TUnion ty1 ty2) ty j) : ws' -> do
      a <- lift freshTVar
      b <- lift freshTVar
      let j' = InfTApp ty1 ty $ bind a $ InfTApp ty2 ty $ bind b $ substBind j (TUnion (TVar a) (TVar b))
      retInf "InfTAppUnion" $ WJug j' : ws'
    WJug (InfTApp (TIntersection _ _) _ _) : _ ->
      msum
        [ ruleInfTAppIntersectionL,
          ruleInfTAppIntersectionR
        ]
    _ -> return mzero
  where
    ret :: String -> [(String, Worklist)] -> LogicT InferMonad [(String, Worklist)]
    ret rule logs = return $ (rule, ws) : logs

    retInf :: String -> Worklist -> LogicT InferMonad [(String, Worklist)]
    retInf rule ws' = infer ws' >>= ret rule

    ruleSubAllL = case ws of
      WJug (Sub (TAll bnd) ty2) : ws' | notAll ty2 -> do
        (a, ty1) <- lift $ unbind bnd
        let ty1' = subst a (ETVar a) ty1
        retInf "SubAllL" $ WJug (Sub ty1' ty2) : WTVar a ETVarBind : ws'
      _ -> mzero

    ruleSubIntersectionL = case ws of
      WJug (Sub (TIntersection ty1 _) ty) : ws' ->
        retInf "SubIntersectionL" $ WJug (Sub ty1 ty) : ws'
      _ -> mzero

    ruleSubIntersectionR = case ws of
      WJug (Sub ty (TIntersection _ ty2)) : ws' ->
        retInf "SubIntersectionR" $ WJug (Sub ty ty2) : ws'
      _ -> mzero

    ruleSubIntersection = case ws of
      WJug (Sub ty (TIntersection ty1 ty2)) : ws' ->
        retInf "SubIntersection" $ WJug (Sub ty ty1) : WJug (Sub ty ty2) : ws'
      _ -> mzero

    ruleSubUnionL = case ws of
      WJug (Sub ty (TUnion ty1 _)) : ws' ->
        retInf "SubUnionL" $ WJug (Sub ty ty1) : ws'
      _ -> mzero

    ruleSubUnionR = case ws of
      WJug (Sub ty (TUnion _ ty2)) : ws' ->
        retInf "SubUnionR" $ WJug (Sub ty ty2) : ws'
      _ -> mzero

    ruleSubUnion = case ws of
      WJug (Sub (TUnion ty1 ty2) ty) : ws' ->
        retInf "SubUnion" $ WJug (Sub ty1 ty) : WJug (Sub ty2 ty) : ws'
      _ -> mzero

    ruleChkIntersection = case ws of
      WJug (Chk tm (TIntersection ty1 ty2)) : ws' ->
        retInf "ChkIntersection" $ WJug (Chk tm ty1) : WJug (Chk tm ty2) : ws'
      _ -> mzero

    ruleChkUnionL = case ws of
      WJug (Chk tm (TUnion ty1 _)) : ws' ->
        retInf "ChkUnionL" $ WJug (Chk tm ty1) : ws'
      _ -> mzero

    ruleChkUnionR = case ws of
      WJug (Chk tm (TUnion _ ty2)) : ws' ->
        retInf "ChkUnionR" $ WJug (Chk tm ty2) : ws'
      _ -> mzero

    ruleChkSub = case ws of
      WJug (Chk tm ty) : ws' -> do
        a <- lift freshTVar
        retInf "ChkSub" $ WJug (Inf tm (bind a (Sub (TVar a) ty))) : ws'
      _ -> mzero

    ruleMatchIntersectionL = case ws of
      WJug (Match (TIntersection ty1 _) j) : ws' ->
        retInf "MatchIntersectionL" $ WJug (Match ty1 j) : ws'
      _ -> mzero

    ruleMatchIntersectionR = case ws of
      WJug (Match (TIntersection _ ty2) j) : ws' ->
        retInf "MatchIntersectionR" $ WJug (Match ty2 j) : ws'
      _ -> mzero

    ruleInfTAppIntersectionL = case ws of
      WJug (InfTApp (TIntersection ty1 _) ty j) : ws' ->
        retInf "InfTAppIntersectionL" $ WJug (InfTApp ty1 ty j) : ws'
      _ -> mzero

    ruleInfTAppIntersectionR = case ws of
      WJug (InfTApp (TIntersection _ ty2) ty j) : ws' ->
        retInf "InfTAppIntersectionR" $ WJug (InfTApp ty2 ty j) : ws'
      _ -> mzero

runInfer :: Worklist -> Either [String] [String]
runInfer ws = case runInferMonad $ observeT $ infer ws of
  Left errs -> Left errs
  Right (logs, _) -> Right $ map (\(rule, wl) -> rule ++ ": " ++ show wl) logs

runIU :: Trm -> Either [String] [String]
runIU = runInfer . initWL
