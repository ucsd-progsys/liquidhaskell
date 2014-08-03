{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}

module Language.Haskell.Liquid.Predicates (
  generatePredicates
  ) where


import           CoreSyn
import qualified DataCon                              as TC
import           IdInfo
import           Name                                 (mkInternalName)
import           OccName                              (mkTyVarOcc)
import           SrcLoc
import           Unique                               (initTyVarUnique)
import           Var

import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types              as F
import           Language.Haskell.Liquid.Bare
import           Language.Haskell.Liquid.GhcInterface
import           Language.Haskell.Liquid.PredType     hiding (exprType)
import           Language.Haskell.Liquid.RefType      hiding (generalize)
import           Language.Haskell.Liquid.Types

import           Control.Applicative                  ((<$>))

----------------------------------------------------------------------
---- Predicate Environments ------------------------------------------
----------------------------------------------------------------------

-- | @generatePredicates@ inserts dummy predicate applications into
--   the source @[Bind CoreBndr]@ to facilitate abstract-predicate
--   instantiation in a manner symmetric to vanilla polymorphic
--   instantiation at type-instantiation sites.

generatePredicates ::  GhcInfo -> (F.SEnv PrType)
generatePredicates info = nPd
  where
    nPd                 = getNeedPd $ spec info

getNeedPd spec          = F.fromListSEnv bs
    where
      bs                = mapFst F.symbol <$> (dcs ++ assms)
      dcs               = concatMap mkDataConIdsTy pcs
      pcs               = [(x, dataConPtoPredTy x y) | (x, y) <- dconsP spec]
      assms             = mapSnd (mapReft ur_pred . val) <$> tySigs spec

dataConPtoPredTy :: TC.DataCon -> DataConP -> PrType
dataConPtoPredTy dc = fmap ur_pred . dataConPSpecType dc

-- NUKE addPredApp γ (NonRec b e) = NonRec b $ thd3 $ pExpr γ e
-- NUKE addPredApp γ (Rec ls)     = Rec $ zip xs es'
-- NUKE   where es' = (thd3. pExpr γ) <$> es
-- NUKE         (xs, es) = unzip ls
-- NUKE 
-- NUKE pExpr γ e
-- NUKE   | a == 0 && p /= 0 = (0, 0, foldl App e' ps)
-- NUKE   | otherwise        = (0, p, e')
-- NUKE  where
-- NUKE    (a, p, e')        = pExprN γ e
-- NUKE    ps                = nArgs p -- stringArg . ("p" ++) . show <$> [1 .. p]
-- NUKE 
-- NUKE pExprN γ (App e1 e2) =
-- NUKE   let (_, _, e2') = pExprN γ e2 in
-- NUKE   if (a1 == 0)
-- NUKE    then (0, 0, (App (foldl App e1' ps) e2'))
-- NUKE    else (a1-1, p1, (App e1' e2'))
-- NUKE  where
-- NUKE    ps            = nArgs p1
-- NUKE    (a1, p1, e1') = pExprN γ e1
-- NUKE 
-- NUKE pExprN γ (Lam x e) = (0, 0, Lam x e')
-- NUKE   where (_, _, e') = pExpr γ e
-- NUKE 
-- NUKE pExprN γ (Var v) | isSpecialId γ v
-- NUKE   = (a, p, (Var v))
-- NUKE     where (a, p) = varPredArgs γ v
-- NUKE 
-- NUKE pExprN _ (Var v) = (0, 0, Var v)
-- NUKE 
-- NUKE pExprN γ (Let (NonRec x1 e1) e) = (0, 0, Let (NonRec x1 e1') e')
-- NUKE  where (_, _, e') = pExpr γ e
-- NUKE        (_, _, e1') = pExpr γ e1
-- NUKE 
-- NUKE pExprN γ (Let bds e) = (0, 0, Let bds' e')
-- NUKE  where (_, _, e') = pExpr γ e
-- NUKE        bds' = addPredApp γ bds
-- NUKE pExprN γ (Case e b t es) = (0, 0, Case e' b t (map (pExprNAlt γ ) es))
-- NUKE   where e' = thd3 $ pExpr γ e
-- NUKE 
-- NUKE pExprN γ (Tick n e) = (a, p, Tick n e')
-- NUKE  where (a, p, e') = pExprN γ e
-- NUKE 
-- NUKE pExprN _ e@(Type _) = (0, 0, e)
-- NUKE pExprN _ e@(Lit _)  = (0, 0, e)
-- NUKE pExprN _ e = (0, 0, e)
-- NUKE 
-- NUKE pExprNAlt γ (x, y, e) = (x, y, e')
-- NUKE  where e' = thd3 $ pExpr γ e


-- NUKE -- | @nArgs@ returns a list of dummy (value) variables that are inserted
-- NUKE --   at predicate application sites.
-- NUKE nArgs n     = stringArg . ("p" ++) . show <$> [1 .. n]

-- NUKE stringArg s = Var $ mkGlobalVar idDet name predType idInfo
-- NUKE   where
-- NUKE     idDet   = coVarDetails
-- NUKE     name    = mkInternalName initTyVarUnique occ noSrcSpan
-- NUKE     occ     = mkTyVarOcc s
-- NUKE     idInfo  = vanillaIdInfo

-- NUKE isSpecialId γ x       = pl /= 0
-- NUKE   where
-- NUKE     (_, pl)           = varPredArgs γ x

-- NUKE varPredArgs γ x       = varPredArgs_ (F.lookupSEnv (F.symbol x) γ)
-- NUKE 
-- NUKE varPredArgs_ Nothing  = (0, 0)
-- NUKE varPredArgs_ (Just t) = (length $ ty_vars trep, length $ ty_preds trep)
-- NUKE   where
-- NUKE     trep              = toRTypeRep t

