{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, UndecidableInstances #-}
module Language.Haskell.Liquid.PredType (
    PrType
  , TyConP (..), DataConP (..)
  , splitVsPs, typeAbsVsPs, splitArgsRes
  , generalize, generalizeArgs
  , dataConTy, dataConPtoPredTy
  , removeExtPreds
  ) where

import Class
import CoreSyn
import Type
import TcType
import TypeRep
import qualified TyCon as TC
import Literal
import Class
import Var 
import Unique (getUnique)

import Outputable hiding (empty)

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S
import Data.List  (foldl')
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Fixpoint
import Language.Haskell.Liquid.RefType 
import Language.Haskell.Liquid.GhcMisc

import Data.Bifunctor
import Control.Applicative  ((<$>))
import Control.DeepSeq
import Data.Data

data TyConP = TyConP { freeTyVarsTy :: ![RTyVar]
                     , freePredTy   :: ![(PVar Type)]
                     }

data DataConP = DataConP { freeTyVars :: ![RTyVar]
                         , freePred   :: ![(PVar Type)]
                         , tyArgs     :: ![(Symbol, PrType)]
                         , tyRes      :: !PrType
                         }

dataConPtoPredTy :: DataConP -> PrType
dataConPtoPredTy x@(DataConP vs ps yts rt) = {- traceShow ("dataConPtoPredTy: " ++ show x) $ -}  t3						
  where t1 = foldl' (\t2 (x, t1) -> RFun (RB x) t1 t2) rt yts 
        t2 = foldr RAll t1 $ RP <$> ps
        t3 = foldr RAll t2 $ RV <$> vs

instance Outputable TyConP where
  ppr (TyConP vs ps) = (parens $ hsep (punctuate comma (map ppr vs))) <+>
                       (parens $ hsep (punctuate comma (map ppr ps)))

instance Show TyConP where
 show = showSDoc . ppr

instance Outputable DataConP where
 ppr (DataConP vs ps yts t) 
   = (parens $ hsep (punctuate comma (map ppr vs))) <+>
     (parens $ hsep (punctuate comma (map ppr ps))) <+>
     (parens $ hsep (punctuate comma (map ppr yts))) <+>
     ppr t

instance Show DataConP where
 show = showSDoc . ppr

removeExtPreds (RAll (RP pv)  t) = removeExtPreds (subp (M.singleton pv pdTrue) t) 
-- removeExtPreds t@(RAll (RV _) _) = t
removeExtPreds t                 = t

dataConTy m (TyVarTy v)            
  = M.findWithDefault (rVar v pdTrue) (RTV v) m
dataConTy m (FunTy t1 t2)          
  = RFun (RB dummySymbol) (dataConTy m t1) (dataConTy m t2)
dataConTy m (ForAllTy α t)          
  = RAll (rTyVar α) (dataConTy m t)
dataConTy m t
  | isPredTy t
  = ofPredTree $ classifyPredType t
dataConTy m (TyConApp c ts)        
  = rApp c (dataConTy m <$> ts) [] pdTrue
dataConTy _ t
  = error "ofTypePAppTy"

--ofTypeP (TyVarTy α)            
--  = rVar α pdTrue
--ofTypeP (FunTy t1 t2)          
--  = RFun (RB dummySymbol) (ofTypeP t1) (ofTypeP t2)
--ofTypeP (ForAllTy α t)          
--  = RAll (rTyVar α) (ofTypeP t)
--ofTypeP t
--  | isPredTy t
--  = ofPredTree $ classifyPredType t
--ofTypeP (TyConApp c ts)
--  | TC.isSynTyCon c
--  = ofTypeP $ substTyWith αs ts τ
--  | otherwise
--  = rApp c (ofTypeP <$> ts) [] pdTrue
--  where (αs, τ) = TC.synTyConDefn c
--ofTypeP t
--	= error "ofTypePAppTy"
--
--ofPredTree (ClassPred c ts)
--  = RCls c (ofType <$> ts)
--ofPredTree _
--  = error "ofPredTree"

generalize     = generalize_ freePreds
generalizeArgs = generalize_ freeArgPreds

generalize_ f t = typeAbsVsPs t' vs ps
  where (vs, ps', t') = splitVsPs t
        ps            = (S.toList (f t)) ++ ps'

freeArgPreds (RFun _ t1 t2)  = freePreds t1 -- RJ: UNIFY What about t2?
freeArgPreds (RAll _ t)      = freeArgPreds t
freeArgPreds t               = freePreds t

-- freePreds :: PrType -> S.Set (Predicate Type)
freePreds (RVar _ p)       = S.fromList $ pvars p
freePreds (RAll (RV _) t)  = freePreds t -- UNIFY? remove binder?
freePreds (RAll (RP p) t)  = S.delete p $ freePreds t 
freePreds (RCls _ ts)      = foldl' (\z t -> S.union z (freePreds t)) S.empty ts
freePreds (RFun _ t1 t2)   = S.union (freePreds t1) (freePreds t2)
freePreds (RApp _ ts ps p) = unions ((S.fromList (concatMap pvars (p:ps))) : (freePreds <$> ts))

--freePreds (PrLit _ p)    = S.fromList $ pvars p
--normalizeP (PdVar pv)    = [pv]
--normalizeP (PdAnd p1 p2) = normalizeP p1 ++ normalizeP p2
--normalizeP _             = []

showTyV v = showSDoc $ ppr v <> ppr (varUnique v) <> text "  "
showTy (TyVarTy v) = showSDoc $ ppr v <> ppr (varUnique v) <> text "  "
showTy t = showSDoc $ ppr t

-- RJ: UNIFY: BUG? Do we want to rename bound vars? Probably not.
--mapTy f (RFun (RB s) t1 t2) = PrFun (RB $ f s) (mapTy f t1) (mapTy f t2)
--mapTy f (PrAll a t)         = PrAll a (mapTy f t)
--mapTy f (PrAllPr p t)       = PrAllPr p (mapTy f t)
--mapTy f (PrLit l p)         = PrLit l p
--mapTy f t@(RVar a p)        = t 
--mapTy f (PrTyCon c ts ps p) = PrTyCon c ((mapTy f) <$> ts) ps p
--mapTy f (PrClass c ts)      = PrClass c (mapTy f <$> ts)
typeAbsVsPs t vs ps = t2
  where t1 = foldr RAll t  (RP <$> ps)  -- RJ: UNIFY reverse?
        t2 = foldr RAll t1 (RV <$> vs)

splitVsPs t = go ([], []) t
  where go (vs, pvs) (RAll (RV v)  t) = go (v:vs, pvs)  t
        go (vs, pvs) (RAll (RP pv) t) = go (vs, pv:pvs) t
        go (vs, pvs) t                = (reverse vs, reverse pvs, t)

splitArgsRes (RFun _ t1 t2) = (t1:t1', t2')
  where (t1', t2') = splitArgsRes t2
splitArgsRes t = ([], t)

----------------------------------------------------------------------
-- UNIFY: MOVE INTO Predicates.hs
----------------------------------------------------------------------


