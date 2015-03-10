{-# LANGUAGE IncoherentInstances       #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts          #-} 
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE PatternGuards             #-}

-- | Refinement Types. Mostly mirroring the GHC Type definition, but with
--   room for refinements of various sorts.

-- TODO: Desperately needs re-organization.
module Language.Haskell.Liquid.RefType (

  -- * Functions for lifting Reft-values to Spec-values
    uTop, uReft, uRType, uRType', uRTypeGen, uPVar
  
  -- * Applying a solution to a SpecType 
  , applySolution

  -- * Functions for decreasing arguments
  , isDecreasing, makeDecrType
  , makeLexRefa

  -- * Functions for manipulating `Predicate`s
  , pdVar
  , findPVar
  , freeTyVars, tyClasses, tyConName

  -- TODO: categorize these!
  , ofType, toType
  , rTyVar, rVar, rApp, rEx 
  , symbolRTyVar
  , addTyConInfo
  -- , expandRApp
  , appRTyCon
  , typeSort, typeUniqueSymbol
  , strengthen
  , generalize, normalizePds
  , subts, subvPredicate, subvUReft
  , subsTyVar_meet, subsTyVars_meet, subsTyVar_nomeet, subsTyVars_nomeet
  , dataConSymbol, dataConMsReft, dataConReft  
  , classBinds
 
  -- * Manipulating Refinements in RTypes 
  , rTypeSortedReft
  , rTypeSort
  , shiftVV

  , mkDataConIdsTy
  , mkTyConInfo 
  ) where

import WwLib
import FamInstEnv (emptyFamInstEnv)
import Var
import GHC              hiding (Located)
import DataCon
import qualified TyCon  as TC
import TypeRep          hiding (maybeParen, pprArrowChain)  
import Type             (splitFunTys, expandTypeSynonyms, substTyWith, isClassPred)
import TysWiredIn       (listTyCon, intDataCon, trueDataCon, falseDataCon, 
                         intTyCon, charTyCon)

import           Data.Monoid      hiding ((<>))
import           Data.Maybe               (fromMaybe, isJust)
import           Data.Hashable
import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S 
import qualified Data.List as L
import Control.Applicative  hiding (empty)   
import Control.DeepSeq
import Control.Monad  (void)
import Text.Printf
import Text.PrettyPrint.HughesPJ

import Language.Haskell.Liquid.PrettyPrint
import qualified Language.Fixpoint.Types as F
import Language.Fixpoint.Types hiding (shiftVV, Predicate)
import Language.Haskell.Liquid.Types hiding (R, DataConP (..), sort)

import Language.Haskell.Liquid.Variance

import Language.Haskell.Liquid.Misc
import Language.Fixpoint.Misc
import Language.Haskell.Liquid.GhcMisc (typeUniqueString, tvId, showPpr, stringTyVar)
import Language.Fixpoint.Names (listConName, tupConName)
import Data.List (sort, foldl')


pdVar v        = Pr [uPVar v]

findPVar :: [PVar (RType c tv ())] -> UsedPVar -> PVar (RType c tv ())
findPVar ps p 
  = PV name ty v (zipWith (\(_, _, e) (t, s, _) -> (t, s, e)) (pargs p) args)
  where PV name ty v args = fromMaybe (msg p) $ L.find ((== pname p) . pname) ps 
        msg p = errorstar $ "RefType.findPVar" ++ showpp p ++ "not found"

-- | Various functions for converting vanilla `Reft` to `Spec`

uRType          ::  RType c tv a -> RType c tv (UReft a)
uRType          = fmap uTop 

uRType'         ::  RType c tv (UReft a) -> RType c tv a 
uRType'         = fmap ur_reft

uRTypeGen       :: Reftable b => RType c tv a -> RType c tv b
uRTypeGen       = fmap $ const mempty

uPVar           :: PVar t -> UsedPVar
uPVar           = void -- fmap (const ())

uReft           ::  (Symbol, [Refa]) -> UReft Reft 
uReft           = uTop . Reft  

uTop            ::  r -> UReft r
uTop r          = U r mempty mempty

--------------------------------------------------------------------
-------------- (Class) Predicates for Valid Refinement Types -------
--------------------------------------------------------------------

-- Monoid Instances ---------------------------------------------------------


instance ( SubsTy tv (RType c tv ()) (RType c tv ())
         , SubsTy tv (RType c tv ()) c
         , RefTypable c tv ()
         , RefTypable c tv r 
         , PPrint (RType c tv r)
         )
        => Monoid (RType c tv r)  where
  mempty  = errorstar "mempty: RType"
  mappend = strengthenRefType

-- MOVE TO TYPES
instance ( SubsTy tv (RType c tv ()) (RType c tv ())
         , SubsTy tv (RType c tv ()) c
         , Reftable r 
         , RefTypable c tv ()
         , RefTypable c tv (UReft r)) 
         => Monoid (Ref (RType c tv ()) r (RType c tv (UReft r))) where
  mempty      = errorstar "mempty: RType 2"
  mappend _ _ = errorstar "mappend: RType 2"
  
instance ( Monoid r, Reftable r, RefTypable b c r, RefTypable b c ()) => Monoid (RTProp b c r) where
  mempty         = errorstar "mempty: RTProp"

  mappend (RPropP s1 r1) (RPropP s2 r2) 
    | isTauto r1 = RPropP s2 r2
    | isTauto r2 = RPropP s1 r1
    | otherwise  = RPropP (s1 ++ s2) $ r1 `meet` r2
  
  mappend (RProp s1 t1) (RProp s2 t2) 
    | isTrivial t1 = RProp s2 t2
    | isTrivial t2 = RProp s1 t1
    | otherwise    = RProp (s1 ++ s2) $ t1  `strengthenRefType` t2

  mappend _ _ = errorstar "Reftable.mappend on invalid inputs"

instance (Reftable r, RefTypable c tv r, RefTypable c tv ()) => Reftable (RTProp c tv r) where
  isTauto (RPropP _ r) = isTauto r
  isTauto (RProp  _ t) = isTrivial t
  isTauto (RHProp _ _) = errorstar "RefType: Reftable isTauto in RHProp"
  top (RProp xs t)     = RProp xs $ mapReft top t 
  top _                = errorstar "RefType: Reftable top"  
  ppTy (RPropP _ r) d  = ppTy r d
  ppTy (RProp  _ _) _  = errorstar "RefType: Reftable ppTy in RProp"
  ppTy (RHProp _ _) _  = errorstar "RefType: Reftable ppTy in RProp"
  toReft               = errorstar "RefType: Reftable toReft"
  params               = errorstar "RefType: Reftable params for Ref"
  bot                  = errorstar "RefType: Reftable bot    for Ref"
  ofReft               = errorstar "RefType: Reftable ofReft for Ref"


----------------------------------------------------------------------------
-- | Subable Instances -----------------------------------------------------
----------------------------------------------------------------------------

instance Subable (RRProp Reft) where
  syms (RPropP ss r)     = (fst <$> ss) ++ syms r
  syms (RProp ss t)      = (fst <$> ss) ++ syms t
  syms _                 = error "TODO:EFFECTS"
  
  subst su (RPropP ss r) = RPropP (mapSnd (subst su) <$> ss) $ subst su r 
  subst su (RProp ss r)  = RProp  (mapSnd (subst su) <$> ss) $ subst su r
  subst _  _             = error "TODO:EFFECTS"
  
  substf f (RPropP ss r) = RPropP (mapSnd (substf f) <$> ss) $ substf f r
  substf f (RProp  ss r) = RProp  (mapSnd (substf f) <$> ss) $ substf f r
  substf _ _             = error "TODO:EFFECTS"
  substa f (RPropP ss r) = RPropP (mapSnd (substa f) <$> ss) $ substa f r
  substa f (RProp  ss r) = RProp  (mapSnd (substa f) <$> ss) $ substa f r
  substa _ _             = error "TODO:EFFECTS"
  
-------------------------------------------------------------------------------
-- | Reftable Instances -------------------------------------------------------
-------------------------------------------------------------------------------

instance (PPrint r, Reftable r) => Reftable (RType RTyCon RTyVar r) where
  isTauto     = isTrivial
  ppTy        = errorstar "ppTy RProp Reftable" 
  toReft      = errorstar "toReft on RType"
  params      = errorstar "params on RType"
  bot         = errorstar "bot on RType"
  ofReft      = errorstar "ofReft on RType"



-------------------------------------------------------------------------------
-- | RefTypable Instances -----------------------------------------------------
-------------------------------------------------------------------------------

-- MOVE TO TYPES
instance Fixpoint String where
  toFix = text 

-- MOVE TO TYPES
instance Fixpoint Class where
  toFix = text . showPpr

-- MOVE TO TYPES
instance (TyConable c, Reftable r, PPrint r, PPrint c) => RefTypable c Symbol r where
--   ppCls   = ppClassSymbol
  ppRType = ppr_rtype ppEnv

-- MOVE TO TYPES
instance (Reftable r, PPrint r) => RefTypable RTyCon RTyVar r where
--   ppCls   = ppClassClassPred
  ppRType = ppr_rtype ppEnv

-- MOVE TO TYPES
class FreeVar a v where 
  freeVars :: a -> [v]

-- MOVE TO TYPES
instance FreeVar RTyCon RTyVar where
  freeVars = (RTV <$>) . tyConTyVars . rtc_tc

-- MOVE TO TYPES
instance FreeVar LocSymbol Symbol where
  freeVars _ = []


-- Eq Instances ------------------------------------------------------

-- MOVE TO TYPES
instance (RefTypable c tv ()) => Eq (RType c tv ()) where
  (==) = eqRSort M.empty 

eqRSort m (RAllP _ t) (RAllP _ t') 
  = eqRSort m t t'
eqRSort m (RAllS _ t) (RAllS _ t') 
  = eqRSort m t t'
eqRSort m (RAllP _ t) t' 
  = eqRSort m t t'
eqRSort m (RAllT a t) (RAllT a' t')
  | a == a'
  = eqRSort m t t'
  | otherwise
  = eqRSort (M.insert a' a m) t t' 
eqRSort m (RFun _ t1 t2 _) (RFun _ t1' t2' _) 
  = eqRSort m t1 t1' && eqRSort m t2 t2'
eqRSort m (RAppTy t1 t2 _) (RAppTy t1' t2' _) 
  = eqRSort m t1 t1' && eqRSort m t2 t2'
eqRSort m (RApp c ts _ _) (RApp c' ts' _ _)
  = c == c' && length ts == length ts' && and (zipWith (eqRSort m) ts ts')
eqRSort m (RVar a _) (RVar a' _)
  = a == M.lookupDefault a' a' m 
eqRSort _ (RHole _) _
  = True
eqRSort _ _         (RHole _)
  = True
eqRSort _ _ _
  = False

--------------------------------------------------------------------
-- | Wrappers for GHC Type Elements --------------------------------
--------------------------------------------------------------------

instance Eq Predicate where
  (==) = eqpd

eqpd (Pr vs) (Pr ws) 
  = and $ (length vs' == length ws') : [v == w | (v, w) <- zip vs' ws']
    where vs' = sort vs
          ws' = sort ws


instance Eq RTyVar where
  RTV α == RTV α' = tvId α == tvId α'

instance Ord RTyVar where
  compare (RTV α) (RTV α') = compare (tvId α) (tvId α')

instance Hashable RTyVar where
  hashWithSalt i (RTV α) = hashWithSalt i α

instance Ord RTyCon where
  compare x y = compare (rtc_tc x) (rtc_tc y)

instance Hashable RTyCon where
  hashWithSalt i = hashWithSalt i . rtc_tc  

--------------------------------------------------------------------
---------------------- Helper Functions ----------------------------
--------------------------------------------------------------------

rVar        = (`RVar` mempty) . RTV 
rTyVar      = RTV

symbolRTyVar = rTyVar . stringTyVar . symbolString

normalizePds t = addPds ps t'
  where (t', ps) = nlzP [] t

rPred     = RAllP
rEx xts t = foldr (\(x, tx) t -> REx x tx t) t xts   
rApp c    = RApp (RTyCon c [] (mkTyConInfo c [] [] Nothing)) 

--- NV TODO : remove this code!!!

addPds ps (RAllT v t) = RAllT v $ addPds ps t
addPds ps t           = foldl' (flip rPred) t ps

nlzP ps t@(RVar _ _ ) 
 = (t, ps)
nlzP ps (RFun b t1 t2 r) 
 = (RFun b t1' t2' r, ps ++ ps1 ++ ps2)
  where (t1', ps1) = nlzP [] t1
        (t2', ps2) = nlzP [] t2
nlzP ps (RAppTy t1 t2 r) 
 = (RAppTy t1' t2' r, ps ++ ps1 ++ ps2)
  where (t1', ps1) = nlzP [] t1
        (t2', ps2) = nlzP [] t2
nlzP ps (RAllT v t )
 = (RAllT v t', ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@(RApp _ _ _ _)
 = (t, ps)
nlzP ps (RAllS _ t)
 = (t, ps)
nlzP ps (RAllP p t)
 = (t', [p] ++ ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@(REx _ _ _) 
 = (t, ps) 
nlzP ps t@(RRTy _ _ _ t') 
 = (t, ps ++ ps')
 where ps' = snd $ nlzP [] t'
nlzP ps t@(RAllE _ _ _) 
 = (t, ps) 
nlzP _ t
 = errorstar $ "RefType.nlzP: cannot handle " ++ show t

-- NEWISH: with unifying type variables: causes big problems with TUPLES?
--strengthenRefType t1 t2 = maybe (errorstar msg) (strengthenRefType_ t1) (unifyShape t1 t2)
--  where msg = printf "strengthen on differently shaped reftypes \nt1 = %s [shape = %s]\nt2 = %s [shape = %s]" 
--                 (render t1) (render (toRSort t1)) (render t2) (render (toRSort t2))

-- OLD: without unifying type variables, but checking α-equivalence
strengthenRefType t1 t2 
  | eqt t1 t2 
  = strengthenRefType_ t1 t2
  | otherwise
  = errorstar msg 
  where 
    eqt t1 t2 = {- render -} toRSort t1 == {- render -} toRSort t2
    msg       = printf "strengthen on differently shaped reftypes \nt1 = %s [shape = %s]\nt2 = %s [shape = %s]" 
                  (showpp t1) (showpp (toRSort t1)) (showpp t2) (showpp (toRSort t2))

         
-- strengthenRefType_ :: RefTypable c tv r => RType c tv r -> RType c tv r -> RType c tv r
strengthenRefType_ (RAllT a1 t1) (RAllT _ t2)
  = RAllT a1 $ strengthenRefType_ t1 t2

strengthenRefType_ (RAllP p1 t1) (RAllP _ t2)
  = RAllP p1 $ strengthenRefType_ t1 t2

strengthenRefType_ (RAllS s t1) t2
  = RAllS s $ strengthenRefType_ t1 t2

strengthenRefType_ t1 (RAllS s t2)
  = RAllS s $ strengthenRefType_ t1 t2

strengthenRefType_ (RAppTy t1 t1' r1) (RAppTy t2 t2' r2) 
  = RAppTy t t' (r1 `meet` r2)
    where t  = strengthenRefType_ t1 t2
          t' = strengthenRefType_ t1' t2'

strengthenRefType_ (RFun x1 t1 t1' r1) (RFun x2 t2 t2' r2) 
  = RFun x1 t t' (r1 `meet` r2)
    where t  = strengthenRefType_ t1 t2
          t' = strengthenRefType_ t1' $ subst1 t2' (x2, EVar x1)

strengthenRefType_ (RApp tid t1s rs1 r1) (RApp _ t2s rs2 r2)
  = RApp tid ts rs (r1 `meet` r2)
    where ts  = zipWith strengthenRefType_ t1s t2s
          rs  = meets rs1 rs2


strengthenRefType_ (RVar v1 r1)  (RVar _ r2)
  = RVar v1 (r1 `meet` r2)
 
strengthenRefType_ t1 _ 
  = t1

meets [] rs                 = rs
meets rs []                 = rs
meets rs rs' 
  | length rs == length rs' = zipWith meet rs rs'
  | otherwise               = errorstar "meets: unbalanced rs"


strengthen :: Reftable r => RType c tv r -> r -> RType c tv r
strengthen (RApp c ts rs r) r'  = RApp c ts rs (r `meet` r') 
strengthen (RVar a r) r'        = RVar a       (r `meet` r') 
strengthen (RFun b t1 t2 r) r'  = RFun b t1 t2 (r `meet` r')
strengthen (RAppTy t1 t2 r) r'  = RAppTy t1 t2 (r `meet` r')
strengthen t _                  = t 



-------------------------------------------------------------------------
addTyConInfo :: (PPrint r, Reftable r)
             => (M.HashMap TyCon FTycon)
             -> (M.HashMap TyCon RTyCon)
             -> RRType r
             -> RRType r
-------------------------------------------------------------------------
addTyConInfo tce tyi = mapBot (expandRApp tce tyi)

-------------------------------------------------------------------------
expandRApp :: (PPrint r, Reftable r)
           => (M.HashMap TyCon FTycon)
           -> (M.HashMap TyCon RTyCon)
           -> RRType r
           -> RRType r
-------------------------------------------------------------------------
expandRApp tce tyi t@(RApp {}) = RApp rc' ts rs' r
  where
    RApp rc ts rs r            = t
    rc'                        = appRTyCon tce tyi rc as
    pvs                        = rTyConPVs rc'
    rs'                        = applyNonNull rs0 (rtPropPV rc pvs) rs
    rs0                        = rtPropTop <$> pvs
    n                          = length fVs
    fVs                        = tyConTyVars $ rtc_tc rc
    as                         = choosen n ts (rVar <$> fVs)
  
    choosen 0 _ _           = []
    choosen i (x:xs) (_:ys) = x:choosen (i-1) xs ys
    choosen i []     (y:ys) = y:choosen (i-1) [] ys
    choosen _ _ _           = errorstar "choosen: this cannot happen"

expandRApp _ _ t               = t

rtPropTop pv = case ptype pv of
                 PVProp t -> RProp xts $ ofRSort t
                 PVHProp  -> RProp xts $ mempty
               where
                 xts      =  pvArgs pv
                 
rtPropPV rc = safeZipWith msg mkRTProp
  where
    msg     = "appRefts: " ++ showFix rc

mkRTProp pv (RPropP ss r) 
  = RProp ss $ (ofRSort $ pvType pv) `strengthen` r  

mkRTProp pv (RProp ss t) 
  | length (pargs pv) == length ss 
  = RProp ss t
  | otherwise
  = RProp (pvArgs pv) t
    
mkRTProp pv (RHProp ss w) 
  | length (pargs pv) == length ss 
  = RHProp ss w
  | otherwise          
  = RHProp (pvArgs pv) w

pvArgs pv = [(s, t) | (t, s, _) <- pargs pv]    


appRTyCon tce tyi rc ts = RTyCon c ps' (rtc_info rc'')
  where
    c    = rtc_tc rc
    ps'  = subts (zip (RTV <$> αs) ts') <$> rTyConPVs rc'
    ts'  = if null ts then rVar <$> βs else toRSort <$> ts
    rc'  = M.lookupDefault rc c tyi
    αs   = TC.tyConTyVars $ rtc_tc rc'
    βs   = TC.tyConTyVars c
    rc'' = if isNumeric tce rc' then addNumSizeFun rc' else rc'

isNumeric tce c 
  =  fromMaybe (symbolFTycon . dummyLoc $ tyConName (rtc_tc c))
       (M.lookup (rtc_tc c) tce) == intFTyCon

addNumSizeFun c 
  = c {rtc_info = (rtc_info c) {sizeFunction = Just EVar} }


generalize :: (RefTypable c tv r) => RType c tv r -> RType c tv r
generalize t = mkUnivs (freeTyVars t) [] [] t 
         
freeTyVars (RAllP _ t)     = freeTyVars t
freeTyVars (RAllS _ t)     = freeTyVars t
freeTyVars (RAllT α t)     = freeTyVars t L.\\ [α]
freeTyVars (RFun _ t t' _) = freeTyVars t `L.union` freeTyVars t' 
freeTyVars (RApp _ ts _ _) = L.nub $ concatMap freeTyVars ts
freeTyVars (RVar α _)      = [α] 
freeTyVars (RAllE _ _ t)   = freeTyVars t
freeTyVars (REx _ _ t)     = freeTyVars t
freeTyVars (RExprArg _)    = []
freeTyVars (RAppTy t t' _) = freeTyVars t `L.union` freeTyVars t'
freeTyVars (RHole _)       = []
freeTyVars (RRTy e _ _ t)  = L.nub $ concatMap freeTyVars (t:(snd <$> e))


tyClasses (RAllP _ t)     = tyClasses t
tyClasses (RAllS _ t)     = tyClasses t
tyClasses (RAllT _ t)     = tyClasses t
tyClasses (RAllE _ _ t)   = tyClasses t
tyClasses (REx _ _ t)     = tyClasses t
tyClasses (RFun _ t t' _) = tyClasses t ++ tyClasses t'
tyClasses (RAppTy t t' _) = tyClasses t ++ tyClasses t'
tyClasses (RApp c ts _ _) 
  | Just cl <- tyConClass_maybe $ rtc_tc c 
  = [(cl, ts)] 
  | otherwise       
  = []
tyClasses (RVar _ _)      = [] 
tyClasses (RRTy _ _ _ t)  = tyClasses t
tyClasses (RHole _)       = []
tyClasses t               = errorstar ("RefType.tyClasses cannot handle" ++ show t)


----------------------------------------------------------------
---------------------- Strictness ------------------------------
----------------------------------------------------------------

instance (NFData a, NFData b, NFData t) => NFData (Ref t a b) where
  rnf (RPropP s a) = rnf s `seq` rnf a
  rnf (RProp  s b) = rnf s `seq` rnf b
  rnf (RHProp _ _) = errorstar "TODO RHProp.rnf"

instance (NFData b, NFData c, NFData e) => NFData (RType b c e) where
  rnf (RVar α r)       = rnf α `seq` rnf r 
  rnf (RAllT α t)      = rnf α `seq` rnf t
  rnf (RAllP π t)      = rnf π `seq` rnf t
  rnf (RAllS s t)      = rnf s `seq` rnf t
  rnf (RFun x t t' r)  = rnf x `seq` rnf t `seq` rnf t' `seq` rnf r
  rnf (RApp _ ts rs r) = rnf ts `seq` rnf rs `seq` rnf r
  rnf (RAllE x t t')   = rnf x `seq` rnf t `seq` rnf t'
  rnf (REx x t t')     = rnf x `seq` rnf t `seq` rnf t'
  rnf (RExprArg e)     = rnf e
  rnf (RAppTy t t' r)  = rnf t `seq` rnf t' `seq` rnf r
  rnf (RRTy _ r _ t)   = rnf r `seq` rnf t
  rnf (RHole r)        = rnf r

----------------------------------------------------------------
------------------ Printing Refinement Types -------------------
----------------------------------------------------------------

instance Show RTyVar where
  show = showpp

instance PPrint (UReft r) => Show (UReft r) where
  show = showpp

instance (RefTypable c tv r) => PPrint (RType c tv r) where
  pprint = ppRType TopPrec

instance PPrint (RType c tv r) => Show (RType c tv r) where
  show = showpp

instance PPrint (RTProp c tv r) => Show (RTProp c tv r) where
  show = showpp

instance PPrint REnv where
  pprint (REnv m)  = pprint m
 
------------------------------------------------------------------------------------------
-- TODO: Rewrite subsTyvars with Traversable
------------------------------------------------------------------------------------------

subsTyVars_meet       = subsTyVars True
subsTyVars_nomeet     = subsTyVars False
subsTyVar_nomeet      = subsTyVar False
subsTyVar_meet        = subsTyVar True
subsTyVars meet ats t = foldl' (flip (subsTyVar meet)) t ats
subsTyVar meet        = subsFree meet S.empty

subsFree m s z (RAllS l t)         
  = RAllS l (subsFree m s z t)
subsFree m s z@(α, τ,_) (RAllP π t)         
  = RAllP (subt (α, τ) π) (subsFree m s z t)
subsFree m s z (RAllT α t)         
  = RAllT α $ subsFree m (α `S.insert` s) z t
subsFree m s z@(_, _, _) (RFun x t t' r)       
  = RFun x (subsFree m s z t) (subsFree m s z t') r
subsFree m s z@(α, τ, _) (RApp c ts rs r)     
  = RApp (subt z' c) (subsFree m s z <$> ts) (subsFreeRef m s z <$> rs) r  
    where z' = (α, τ) -- UNIFY: why instantiating INSIDE parameters?
subsFree meet s (α', _, t') t@(RVar α r) 
  | α == α' && not (α `S.member` s) 
  = if meet then t' `strengthen` r else t' 
  | otherwise
  = t
subsFree m s z (RAllE x t t')
  = RAllE x (subsFree m s z t) (subsFree m s z t')
subsFree m s z (REx x t t')
  = REx x (subsFree m s z t) (subsFree m s z t')
subsFree m s z@(_, _, _) (RAppTy t t' r)
  = subsFreeRAppTy m s (subsFree m s z t) (subsFree m s z t') r
subsFree _ _ _ t@(RExprArg _)        
  = t
subsFree m s z (RRTy e r o t)        
  = RRTy (mapSnd (subsFree m s z) <$> e) r o (subsFree m s z t)
subsFree _ _ _ t@(RHole _)
  = t

subsFrees m s zs t = foldl' (flip(subsFree m s)) t zs

-- GHC INVARIANT: RApp is Type Application to something other than TYCon
subsFreeRAppTy m s (RApp c ts rs r) t' r'
  = mkRApp m s c (ts ++ [t']) rs r r'
subsFreeRAppTy _ _ t t' r'
  = RAppTy t t' r'

mkRApp m s c ts rs r r'
  | isFun c, [t1, t2] <- ts
  = RFun dummySymbol t1 t2 $ refAppTyToFun r'
  | otherwise 
  = subsFrees m s zs $ RApp c ts rs $ r `meet` r' -- (refAppTyToApp r')
  where
    zs = [(tv, toRSort t, t) | (tv, t) <- zip (freeVars c) ts]

refAppTyToFun r
  | isTauto r = r
  | otherwise = errorstar "RefType.refAppTyToFun"

subsFreeRef m s (α', τ', t')  (RProp ss t) 
  = RProp (mapSnd (subt (α', τ')) <$> ss) $ subsFree m s (α', τ', fmap top t') t
subsFreeRef _ _ (α', τ', _) (RPropP ss r) 
  = RPropP (mapSnd (subt (α', τ')) <$> ss) r
subsFreeRef _ _ _ (RHProp _ _)
  = errorstar "TODO RHProp.subsFreeRef"  

-------------------------------------------------------------------
------------------- Type Substitutions ----------------------------
-------------------------------------------------------------------

subts = flip (foldr subt) 

instance SubsTy tv ty ()   where
  subt _ = id

instance SubsTy tv ty Reft where
  subt _ = id

instance (SubsTy tv ty ty) => SubsTy tv ty (PVKind ty) where
  subt su (PVProp t) = PVProp (subt su t)
  subt _   PVHProp   = PVHProp
  
instance (SubsTy tv ty ty) => SubsTy tv ty (PVar ty) where
  subt su (PV n t v xts) = PV n (subt su t) v [(subt su t, x, y) | (t,x,y) <- xts]

instance SubsTy RTyVar RSort RTyCon where  
   subt z c = RTyCon tc ps' i
     where
       tc   = rtc_tc c
       ps'  = subt z <$> rTyConPVs c
       i    = rtc_info c

-- NOTE: This DOES NOT substitute at the binders
instance SubsTy RTyVar RSort PrType where   
  subt (α, τ) = subsTyVar_meet (α, τ, ofRSort τ)

instance SubsTy RTyVar RSort SpecType where   
  subt (α, τ) = subsTyVar_meet (α, τ, ofRSort τ)

instance SubsTy RTyVar RTyVar SpecType where   
  subt (α, a) = subt (α, RVar a () :: RSort)


instance SubsTy RTyVar RSort RSort where   
  subt (α, τ) = subsTyVar_meet (α, τ, ofRSort τ)

-- Here the "String" is a Bare-TyCon. TODO: wrap in newtype 
instance SubsTy Symbol BSort LocSymbol where
  subt _ t = t

instance SubsTy Symbol BSort BSort where
  subt (α, τ) = subsTyVar_meet (α, τ, ofRSort τ)

instance (SubsTy tv ty (UReft r), SubsTy tv ty (RType c tv ())) => SubsTy tv ty (RTProp c tv (UReft r))  where
  subt m (RPropP ss p) = RPropP ((mapSnd (subt m)) <$> ss) $ subt m p
  subt m (RProp  ss t) = RProp ((mapSnd (subt m)) <$> ss) $ fmap (subt m) t
  subt _ (RHProp _  _) = errorstar "TODO: RHProp.subt"
 
subvUReft     :: (UsedPVar -> UsedPVar) -> UReft Reft -> UReft Reft
subvUReft f (U r p s) = U r (subvPredicate f p) s

subvPredicate :: (UsedPVar -> UsedPVar) -> Predicate -> Predicate 
subvPredicate f (Pr pvs) = Pr (f <$> pvs)

---------------------------------------------------------------

ofType = ofType_ . expandTypeSynonyms 

ofType_ (TyVarTy α)     
  = rVar α
ofType_ (FunTy τ τ')    
  = rFun dummySymbol (ofType_ τ) (ofType_ τ') 
ofType_ (ForAllTy α τ)  
  = RAllT (rTyVar α) $ ofType_ τ  
ofType_ (TyConApp c τs)
  | Just (αs, τ) <- TC.synTyConDefn_maybe c
  = ofType_ $ substTyWith αs τs τ
  | otherwise
  = rApp c (ofType_ <$> τs) [] mempty 
ofType_ (AppTy t1 t2)
  = RAppTy (ofType_ t1) (ofType t2) mempty             
ofType_ (LitTy x)
  = fromTyLit x
  where
    fromTyLit (NumTyLit _) = rApp intTyCon [] [] mempty
    fromTyLit (StrTyLit _) = rApp listTyCon [rApp charTyCon [] [] mempty] [] mempty

----------------------------------------------------------------
------------------- Converting to Fixpoint ---------------------
----------------------------------------------------------------


instance Expression Var where
  expr   = eVar

dataConSymbol ::  DataCon -> Symbol
dataConSymbol = symbol . dataConWorkId

-- TODO: turn this into a map lookup?
dataConReft ::  DataCon -> [Symbol] -> Reft
dataConReft c [] 
  | c == trueDataCon
  = Reft (vv_, [RConc $ eProp vv_]) 
  | c == falseDataCon
  = Reft (vv_, [RConc $ PNot $ eProp vv_]) 
dataConReft c [x] 
  | c == intDataCon 
  = Reft (vv_, [RConc (PAtom Eq (EVar vv_) (EVar x))]) 
dataConReft c _ 
  | not $ isBaseDataCon c
  = mempty
dataConReft c xs
  = Reft (vv_, [RConc (PAtom Eq (EVar vv_) dcValue)])
  where dcValue | null xs && null (dataConUnivTyVars c) 
                = EVar $ dataConSymbol c
                | otherwise
                = EApp (dummyLoc $ dataConSymbol c) (EVar <$> xs)

isBaseDataCon c = and $ isBaseTy <$> dataConOrigArgTys c ++ dataConRepArgTys c

isBaseTy (TyVarTy _)     = True
isBaseTy (AppTy _ _)     = False
isBaseTy (TyConApp _ ts) = and $ isBaseTy <$> ts
isBaseTy (FunTy _ _)     = False
isBaseTy (ForAllTy _ _)  = False
isBaseTy (LitTy _)       = True

vv_ = vv Nothing

dataConMsReft ty ys  = subst su (rTypeReft (ignoreOblig $ ty_res trep)) 
  where trep = toRTypeRep ty
        xs   = ty_binds trep
        ts   = ty_args  trep
        su   = mkSubst $ [(x, EVar y) | ((x, _), y) <- zip (zip xs ts) ys]

---------------------------------------------------------------
---------------------- Embedding RefTypes ---------------------
---------------------------------------------------------------
-- TODO: remove toType, generalize typeSort 
toType  :: (Reftable r, PPrint r) => RRType r -> Type
toType (RFun _ t t' _)   
  = FunTy (toType t) (toType t')
toType (RAllT (RTV α) t)      
  = ForAllTy α (toType t)
toType (RAllP _ t)
  = toType t
toType (RAllS _ t)
  = toType t
toType (RVar (RTV α) _)        
  = TyVarTy α
toType (RApp (RTyCon {rtc_tc = c}) ts _ _)   
  = TyConApp c (toType <$> filter notExprArg ts)
  where
  notExprArg (RExprArg _) = False
  notExprArg _            = True
toType (RAllE _ _ t)
  = toType t
toType (REx _ _ t)
  = toType t
toType (RAppTy t (RExprArg _) _)
  = toType t
toType (RAppTy t t' _)   
  = AppTy (toType t) (toType t')
toType t@(RExprArg _)
  = errorstar $ "CANNOT HAPPEN: RefType.toType called with: " ++ show t
toType (RRTy _ _ _ t)      
  = toType t
toType t
  = errorstar $ "RefType.toType cannot handle: " ++ show t


---------------------------------------------------------------
---------------- Annotations and Solutions --------------------
---------------------------------------------------------------

rTypeSortedReft       ::  (PPrint r, Reftable r) => TCEmb TyCon -> RRType r -> SortedReft
rTypeSortedReft emb t = RR (rTypeSort emb t) (rTypeReft t)

rTypeSort     ::  (PPrint r, Reftable r) => TCEmb TyCon -> RRType r -> Sort
rTypeSort tce = typeSort tce . toType

-------------------------------------------------------------------------------
applySolution :: (Functor f) => FixSolution -> f SpecType -> f SpecType 
-------------------------------------------------------------------------------
applySolution = fmap . fmap . mapReft . map . appSolRefa 
  where 
    appSolRefa _ ra@(RConc _)        = ra 
    -- appSolRefa _ p@(RPvar _)  = p  
    appSolRefa s (RKvar k su)        = RConc $ subst su $ M.lookupDefault PTop k s  
    mapReft f (U (Reft (x, zs)) p s) = U (Reft (x, squishRefas $ f zs)) p s

-------------------------------------------------------------------------------
shiftVV :: SpecType -> Symbol -> SpecType
-------------------------------------------------------------------------------

shiftVV t@(RApp _ ts _ r) vv' 
  = t { rt_args = subst1 ts (rTypeValueVar t, EVar vv') } 
      { rt_reft = (`F.shiftVV` vv') <$> r }

shiftVV t@(RFun _ _ _ r) vv' 
  = t { rt_reft = (`F.shiftVV` vv') <$> r }

shiftVV t@(RAppTy _ _ r) vv' 
  = t { rt_reft = (`F.shiftVV` vv') <$> r }

shiftVV t@(RVar _ r) vv'
  = t { rt_reft = (`F.shiftVV` vv') <$> r }

shiftVV t _ 
  = t -- errorstar $ "shiftVV: cannot handle " ++ showpp t


------------------------------------------------------------------------
---------------- Auxiliary Stuff Used Elsewhere ------------------------
------------------------------------------------------------------------

-- MOVE TO TYPES
instance (Show tv, Show ty) => Show (RTAlias tv ty) where
  show (RTA n as xs t p) = printf "type %s %s %s = %s -- defined at %s" (symbolString n)
                           (L.intercalate " " (show <$> as)) 
                           (L.intercalate " " (show <$> xs))
                           (show t) (show p) 

----------------------------------------------------------------
------------ From Old Fixpoint ---------------------------------
----------------------------------------------------------------


typeUniqueSymbol :: Type -> Symbol 
typeUniqueSymbol = symbol . typeUniqueString

typeSort :: TCEmb TyCon -> Type -> Sort 
typeSort tce τ@(ForAllTy _ _) 
  = typeSortForAll tce τ
typeSort tce t@(FunTy _ _)
  = typeSortFun tce t
typeSort tce (TyConApp c τs)
  = fApp (Left $ tyConFTyCon tce c) (typeSort tce <$> τs)
typeSort tce (AppTy t1 t2)
  = fApp (Right $ typeSort tce t1) [typeSort tce t2]
typeSort _ τ
  = FObj $ typeUniqueSymbol τ

tyConFTyCon tce c    = fromMaybe (symbolFTycon $ dummyLoc $ tyConName c) (M.lookup c tce)

typeSortForAll tce τ 
  = genSort $ typeSort tce tbody
  where genSort (FFunc _ t) = FFunc n (sortSubst su <$> t)
        genSort t           = FFunc n [sortSubst su t]
        (as, tbody)         = splitForAllTys τ 
        su                  = M.fromList $ zip sas (FVar <$>  [0..])
        sas                 = (typeUniqueSymbol . TyVarTy) <$> as
        n                   = length as 

tyConName c 
  | listTyCon == c    = listConName
  | TC.isTupleTyCon c = tupConName
  | otherwise         = symbol c

typeSortFun tce t -- τ1 τ2
  = FFunc 0  sos
  where sos  = typeSort tce <$> τs
        τs   = grabArgs [] t
grabArgs τs (FunTy τ1 τ2 )
  | not $ isClassPred τ1 = grabArgs (τ1:τs) τ2
  | otherwise            = grabArgs τs τ2
grabArgs τs τ              = reverse (τ:τs)


mkDataConIdsTy (dc, t) = [expandProductType id t | id <- dataConImplicitIds dc]

expandProductType x t 
  | ofType (varType x) == toRSort t = (x, t)
  | otherwise                       = (x, t')
     where t'         = fromRTypeRep $ trep {ty_binds = xs', ty_args = ts'}
           τs         = fst $ splitFunTys $ toType t
           trep       = toRTypeRep t
           (xs', ts') = unzip $ concatMap mkProductTy $ zip3 τs (ty_binds trep) (ty_args trep)
          
mkProductTy (τ, x, t) = maybe [(x, t)] f $ deepSplitProductType_maybe menv τ
  where f    = ((<$>) ((,) dummySymbol . ofType)) . third4
        menv = (emptyFamInstEnv, emptyFamInstEnv)
          
-----------------------------------------------------------------------------------------
-- | Binders generated by class predicates, typically for constraining tyvars (e.g. FNum)
-----------------------------------------------------------------------------------------

classBinds (RApp c ts _ _) 
   | isFracCls c
   = [(rTyVarSymbol a, trueSortedReft FReal) | (RVar a _) <- ts]
   | isNumCls c
   = [(rTyVarSymbol a, trueSortedReft FNum) | (RVar a _) <- ts]
classBinds _       
  = [] 

rTyVarSymbol (RTV α) = typeUniqueSymbol $ TyVarTy α

-----------------------------------------------------------------------------------------
--------------------------- Termination Predicates --------------------------------------
-----------------------------------------------------------------------------------------

isDecreasing (RApp c _ _ _) 
  = isJust (sizeFunction (rtc_info c)) 
isDecreasing _ 
  = False

makeDecrType = mkDType [] []

mkDType xvs acc [(v, (x, t@(RApp c _ _ _)))] 
  = (x, ) $ t `strengthen` tr
  where tr     = uTop $ Reft (vv, [RConc $ pOr (r:acc)])
        r      = cmpLexRef xvs (v', vv, f)
        v'     = symbol v
        Just f = sizeFunction $ rtc_info c
        vv     = "vvRec"

mkDType xvs acc ((v, (x, (RApp c _ _ _))):vxts)
  = mkDType ((v', x, f):xvs) (r:acc) vxts
  where r      = cmpLexRef xvs  (v', x, f)
        v'     = symbol v
        Just f = sizeFunction $ rtc_info c
mkDType _ _ _
  = errorstar "RefType.mkDType called on invalid input"

cmpLexRef vxs (v, x, g)
  = pAnd $  (PAtom Lt (g x) (g v)) : (PAtom Ge (g x) zero)
         :  [PAtom Eq (f y) (f z) | (y, z, f) <- vxs]
         ++ [PAtom Ge (f y) zero  | (y, _, f) <- vxs]
  where zero = ECon $ I 0

makeLexRefa es' es = uTop $ Reft (vv, [RConc $ PIff (PBexp $ EVar vv) $ pOr rs])
  where rs = makeLexReft [] [] es es'
        vv = "vvRec"

makeLexReft _ acc [] [] 
  = acc
makeLexReft old acc (e:es) (e':es') 
  = makeLexReft ((e,e'):old) (r:acc) es es'
  where 
    r    = pAnd $  (PAtom Lt e' e) 
                :  (PAtom Ge e' zero)
                :  [PAtom Eq o' o    | (o,o') <- old] 
                ++ [PAtom Ge o' zero | (_,o') <- old] 
    zero = ECon $ I 0
makeLexReft _ _ _ _
  = errorstar "RefType.makeLexReft on invalid input"    

-------------------------------------------------------------------------------

mkTyConInfo :: TyCon -> VarianceInfo -> VarianceInfo -> (Maybe (Symbol -> Expr)) -> TyConInfo

mkTyConInfo c usertyvar userprvariance f        
  = TyConInfo (if null usertyvar then defaulttyvar else usertyvar) userprvariance f
  where 
        defaulttyvar      = varSignToVariance <$> [0 ..n]

        varSignToVariance i = case filter (\p -> fst p == i) varsigns of 
                                []       -> Invariant
                                [(_, b)] -> if b then Covariant else Contravariant
                                _        -> Bivariant

        varsigns  = L.nub $ concatMap goDCon $ TC.tyConDataCons c
        initmap   = zip (showPpr <$> tyvars) [0..n]
        mkmap vs  = zip (showPpr <$> vs) (repeat dindex) ++ initmap
        goDCon dc = concatMap (go (mkmap (DataCon.dataConExTyVars dc)) True) (DataCon.dataConOrigArgTys dc)
        go m pos (ForAllTy v t)  = go ((showPpr v, dindex):m) pos t
        go m pos (TyVarTy v)     = [(varLookup (showPpr v) m, pos)]
        go m pos (AppTy t1 t2)   = go m pos t1 ++ go m pos t2
        go m pos (TyConApp _ ts) = concatMap (go m pos) ts
        go m pos (FunTy t1 t2)   = go m (not pos) t1 ++ go m pos t2
        go _ _   (LitTy _)       = []

        varLookup v m = fromMaybe (errmsg v) $ L.lookup v m
        tyvars        = TC.tyConTyVars c
        n             = (TC.tyConArity c) - 1
        errmsg v      = error $ "GhcMisc.getTyConInfo: var not found" ++ showPpr v
        dindex        = -1

