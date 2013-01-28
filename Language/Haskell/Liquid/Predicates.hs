{-# LANGUAGE ScopedTypeVariables, NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, BangPatterns #-}
module Language.Haskell.Liquid.Predicates (
  generatePredicates
  ) where


import Var
import OccName (mkTyVarOcc)
import Name (mkInternalName)
import Unique (initTyVarUnique)
import SrcLoc
import CoreSyn
import qualified DataCon as TC
import IdInfo

import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.GhcInterface
import Language.Haskell.Liquid.PredType hiding (exprType)
import Language.Haskell.Liquid.RefType hiding (generalize) 
import Language.Haskell.Liquid.Misc
import qualified Language.Haskell.Liquid.Fixpoint as F

import Control.Applicative      ((<$>))

----------------------------------------------------------------------
---- Predicate Environments ------------------------------------------
----------------------------------------------------------------------


generatePredicates ::  GhcInfo -> ([CoreSyn.Bind CoreBndr], F.SEnv PrType)
generatePredicates info = {-trace ("Predicates\n" ++ show γ ++ "PredCBS" ++ show cbs')-} (cbs', nPd)
  where -- WHAT?! All the predicate constraint stuff is DEAD CODE?!!
        -- γ    = fmap removeExtPreds (penv $ evalState act (initPI $ tconsP $ spec info))
        -- act  = consAct info
        cbs' = addPredApp nPd <$> cbs info
        nPd  = getNeedPd $ spec info

getNeedPd spec 
  = F.fromListSEnv bs
    where  dcs   = [(TC.dataConWrapId x, dataConPtoPredTy y) | (x, y) <- dconsP spec]
           assms = passm $ tySigs spec 
           bs    = mapFst varSymbol <$> (dcs ++ assms)

dataConPtoPredTy :: DataConP -> PrType
dataConPtoPredTy = fmap ur_pred . dataConPSpecType

passm = fmap (mapSnd (mapReft ur_pred)) 


addPredApp γ (NonRec b e) = NonRec b $ thd3 $ pExpr γ e
addPredApp γ (Rec ls)     = Rec $ zip xs es'
  where es' = (thd3. pExpr γ) <$> es
        (xs, es) = unzip ls

pExpr γ e 
  = if (a == 0 && p /= 0) 
     then (0, 0, foldl App e' ps) 
     else (0, p, e')
 where  (a, p, e') = pExprN γ e
        ps = (\n -> stringArg ("p" ++ show n)) <$> [1 .. p]

pExprN γ (App e1 e2) = 
  let (_, _, e2') = pExprN γ e2 in 
  if (a1 == 0)
   then (0, 0, (App (foldl App e1' ps) e2'))
   else (a1-1, p1, (App e1' e2'))
 where ps = (\n -> stringArg ("p" ++ show n)) <$> [1 .. p1]
       (a1, p1, e1') = pExprN γ e1

pExprN γ (Lam x e) = (0, 0, Lam x e')
  where (_, _, e') = pExpr γ e

pExprN γ (Var v) | isSpecialId γ v
  = (a, p, (Var v))
    where (a, p) = varPredArgs γ v

pExprN _ (Var v) = (0, 0, Var v)

pExprN γ (Let (NonRec x1 e1) e) = (0, 0, Let (NonRec x1 e1') e')
 where (_, _, e') = pExpr γ e
       (_, _, e1') = pExpr γ e1

pExprN γ (Let bds e) = (0, 0, Let bds' e')
 where (_, _, e') = pExpr γ e
       bds' = addPredApp γ bds
pExprN γ (Case e b t es) = (0, 0, Case e' b t (map (pExprNAlt γ ) es))
  where e' = thd3 $ pExpr γ e

pExprN γ (Tick n e) = (a, p, Tick n e')
 where (a, p, e') = pExprN γ e

pExprN _ e@(Type _) = (0, 0, e)
pExprN _ e@(Lit _) = (0, 0, e)
pExprN _ e = (0, 0, e)

pExprNAlt γ (x, y, e) = (x, y, e')
 where e' = thd3 $ pExpr γ e

stringArg s = Var $ mkGlobalVar idDet name predType idInfo
  where  idDet = coVarDetails
         name  = mkInternalName initTyVarUnique occ noSrcSpan
         occ = mkTyVarOcc s 
         idInfo = vanillaIdInfo

isSpecialId γ x = pl /= 0
  where (_, pl) = varPredArgs γ x

varPredArgs γ x = varPredArgs_ (F.lookupSEnv (varSymbol x) γ)
varPredArgs_ Nothing = (0, 0)
varPredArgs_ (Just t) = (length vs, length ps)
  where (vs, ps, _) = bkUniv t

