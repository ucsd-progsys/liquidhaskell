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
{-# LANGUAGE ImplicitParams            #-}

-- | Refinement Types. Mostly mirroring the GHC Type definition, but with
--   room for refinements of various sorts.
-- TODO: Desperately needs re-organization.

module Language.Haskell.Liquid.Types.RefType (

  -- * Functions for lifting Reft-values to Spec-values
    uTop, uReft, uRType, uRType', uRTypeGen, uPVar

  -- * Applying a solution to a SpecType
  , applySolution

  -- * Functions for decreasing arguments
  , isDecreasing, makeDecrType, makeNumEnv
  , makeLexRefa

  -- * Functions for manipulating `Predicate`s
  , pdVar
  , findPVar
  , FreeVar, freeTyVars, tyClasses, tyConName

  -- * Quantifying RTypes
  , quantifyRTy
  , quantifyFreeRTy

  -- TODO: categorize these!
  , ofType, toType
  , bTyVar, rTyVar, rVar, rApp, rEx
  , symbolRTyVar, bareRTyVar
  , addTyConInfo
  , appRTyCon
  , typeSort, typeUniqueSymbol
  , strengthen
  , generalize, normalizePds
  , subts, subvPredicate, subvUReft
  , subsTyVar_meet, subsTyVar_meet', subsTyVar_nomeet
  , subsTyVars_nomeet, subsTyVars_meet
  , dataConMsReft, dataConReft
  , classBinds

  , isSizeable

  -- * Manipulating Refinements in RTypes
  , rTypeSortedReft
  , rTypeSort
  , shiftVV

  , mkDataConIdsTy
  , mkTyConInfo

  , meetable
  , strengthenRefTypeGen
  , strengthenDataConType

  , isBaseTy

  , updateRTVar, isValKind, kindToRType

  ) where

-- import           GHC.Stack
import Prelude hiding (error)
import WwLib
import FamInstEnv (emptyFamInstEnv)
import Name             hiding (varName)
import Var
import Kind 
import GHC              hiding (Located)
import DataCon
import qualified TyCon  as TC
import TypeRep          hiding (maybeParen, pprArrowChain)
import Type             (splitFunTys, expandTypeSynonyms, substTyWith, isClassPred)
import TysWiredIn       (listTyCon, intDataCon, trueDataCon, falseDataCon,
                         intTyCon, charTyCon, typeNatKind, typeSymbolKind, stringTy, intTy)

-- import           Data.Monoid      hiding ((<>))
import           Data.Maybe               (fromMaybe, isJust, fromJust)
import           Data.Hashable
import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S
import qualified Data.List as L

import Control.Monad  (void)
import Text.Printf
import Text.PrettyPrint.HughesPJ

import Language.Haskell.Liquid.Types.Errors
import Language.Haskell.Liquid.Types.PrettyPrint
import qualified Language.Fixpoint.Types as F
import Language.Fixpoint.Types hiding (shiftVV, Predicate, isNumeric)
import Language.Fixpoint.Types.Visitor (mapKVars, Visitable)
import Language.Haskell.Liquid.Types hiding (R, DataConP (..), sort)

import Language.Haskell.Liquid.Types.Variance

import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Types.Names
import Language.Fixpoint.Misc
import Language.Haskell.Liquid.GHC.Misc (typeUniqueString, showPpr, stringTyVar, tyConTyVarsDef)

import Data.List (sort, foldl')

-- -- import Debug.Trace

strengthenDataConType :: Symbolic t
                      => (t, RType c tv (UReft Reft)) -> (t, RType c tv (UReft Reft))
strengthenDataConType (x, t) = (x, fromRTypeRep trep{ty_res = tres})
    where
      trep = toRTypeRep t
      tres = ty_res trep `strengthen` MkUReft (exprReft expr) mempty mempty
      xs   = ty_binds trep
      as   = ty_vars  trep
      x'   = symbol x
      expr | null xs && null as = EVar x'
           | null xs            = mkEApp (dummyLoc x') []
           | otherwise          = mkEApp (dummyLoc x') (EVar <$> xs)

pdVar :: PVar t -> Predicate
pdVar v        = Pr [uPVar v]

findPVar :: [PVar (RType c tv ())] -> UsedPVar -> PVar (RType c tv ())
findPVar ps p = PV name ty v (zipWith (\(_, _, e) (t, s, _) -> (t, s, e)) (pargs p) args)
  where
    PV name ty v args = fromMaybe (msg p) $ L.find ((== pname p) . pname) ps
    msg p = panic Nothing $ "RefType.findPVar" ++ showpp p ++ "not found"

-- | Various functions for converting vanilla `Reft` to `Spec`

uRType          ::  RType c tv a -> RType c tv (UReft a)
uRType          = fmap uTop

uRType'         ::  RType c tv (UReft a) -> RType c tv a
uRType'         = fmap ur_reft

uRTypeGen       :: Reftable b => RType c tv a -> RType c tv b
uRTypeGen       = fmap $ const mempty

uPVar           :: PVar t -> UsedPVar
uPVar           = void

uReft           :: (Symbol, Expr) -> UReft Reft
uReft           = uTop . Reft

uTop            ::  r -> UReft r
uTop r          = MkUReft r mempty mempty

--------------------------------------------------------------------
-------------- (Class) Predicates for Valid Refinement Types -------
--------------------------------------------------------------------


-- Monoid Instances ---------------------------------------------------------

instance ( SubsTy tv (RType c tv ()) (RType c tv ())
         , SubsTy tv (RType c tv ()) c
         , OkRT c tv r
         , FreeVar c tv
         , SubsTy tv (RType c tv ()) r
         , SubsTy tv (RType c tv ()) tv
         , SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ()))
         )
        => Monoid (RType c tv r)  where
  mempty  = panic Nothing "mempty: RType"
  mappend = strengthenRefType


-- MOVE TO TYPES
instance ( SubsTy tv (RType c tv ()) c
         , OkRT c tv r
         , FreeVar c tv
         , SubsTy tv (RType c tv ()) r
         , SubsTy tv (RType c tv ()) (RType c tv ())
         , SubsTy tv (RType c tv ()) tv
         , SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ()))
         )
         => Monoid (RTProp c tv r) where
  mempty         = panic Nothing "mempty: RTProp"

  mappend (RProp s1 (RHole r1)) (RProp s2 (RHole r2))
    | isTauto r1 = RProp s2 (RHole r2)
    | isTauto r2 = RProp s1 (RHole r1)
    | otherwise  = RProp s1 $ RHole $ r1 `meet`
                               (subst (mkSubst $ zip (fst <$> s2) (EVar . fst <$> s1)) r2)

  mappend (RProp s1 t1) (RProp s2 t2)
    | isTrivial t1 = RProp s2 t2
    | isTrivial t2 = RProp s1 t1
    | otherwise    = RProp s1 $ t1  `strengthenRefType`
                                (subst (mkSubst $ zip (fst <$> s2) (EVar . fst <$> s1)) t2)

instance ( OkRT c tv r
         , FreeVar c tv
         , SubsTy tv (RType c tv ()) r
         , SubsTy tv (RType c tv ()) (RType c tv ())
         , SubsTy tv (RType c tv ()) c
         , SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ()))
         ) => Reftable (RTProp c tv r) where
  isTauto (RProp _ (RHole r)) = isTauto r
  isTauto (RProp _ t)         = isTrivial t
  top (RProp _ (RHole _))     = panic Nothing "RefType: Reftable top called on (RProp _ (RHole _))"
  top (RProp xs t)            = RProp xs $ mapReft top t
  ppTy (RProp _ (RHole r)) d  = ppTy r d
  ppTy (RProp _ _) _          = panic Nothing "RefType: Reftable ppTy in RProp"
  toReft                      = panic Nothing "RefType: Reftable toReft"
  params                      = panic Nothing "RefType: Reftable params for Ref"
  bot                         = panic Nothing "RefType: Reftable bot    for Ref"
  ofReft                      = panic Nothing "RefType: Reftable ofReft for Ref"


----------------------------------------------------------------------------
-- | Subable Instances -----------------------------------------------------
----------------------------------------------------------------------------

instance Subable (RRProp Reft) where
  syms (RProp ss (RHole r)) = (fst <$> ss) ++ syms r
  syms (RProp ss t)      = (fst <$> ss) ++ syms t


  subst su (RProp ss (RHole r)) = RProp (mapSnd (subst su) <$> ss) $ RHole $ subst su r
  subst su (RProp ss r)  = RProp  (mapSnd (subst su) <$> ss) $ subst su r


  substf f (RProp ss (RHole r)) = RProp (mapSnd (substf f) <$> ss) $ RHole $ substf f r
  substf f (RProp ss r) = RProp  (mapSnd (substf f) <$> ss) $ substf f r

  substa f (RProp ss (RHole r)) = RProp (mapSnd (substa f) <$> ss) $ RHole $ substa f r
  substa f (RProp ss r) = RProp  (mapSnd (substa f) <$> ss) $ substa f r


-------------------------------------------------------------------------------
-- | Reftable Instances -------------------------------------------------------
-------------------------------------------------------------------------------

instance (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r) => Reftable (RType RTyCon RTyVar r) where
  isTauto     = isTrivial
  ppTy        = panic Nothing "ppTy RProp Reftable"
  toReft      = panic Nothing "toReft on RType"
  params      = panic Nothing "params on RType"
  bot         = panic Nothing "bot on RType"
  ofReft      = panic Nothing "ofReft on RType"


-- MOVE TO TYPES
instance Fixpoint String where
  toFix = text

-- MOVE TO TYPES
instance Fixpoint Class where
  toFix = text . showPpr

-- MOVE TO TYPES
class FreeVar a v where
  freeVars :: a -> [v]

-- MOVE TO TYPES
instance FreeVar RTyCon RTyVar where
  freeVars = (RTV <$>) . tyConTyVarsDef . rtc_tc

-- MOVE TO TYPES
instance FreeVar BTyCon BTyVar where
  freeVars _ = []

-- Eq Instances ------------------------------------------------------

-- MOVE TO TYPES
instance (Eq c, Eq tv, Hashable tv) => Eq (RType c tv ()) where
  (==) = eqRSort M.empty

eqRSort :: (Eq a, Eq k, Hashable k)
        => M.HashMap k k -> RType a k t -> RType a k t1 -> Bool
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
  = eqRSort (M.insert (ty_var_value a') (ty_var_value a) m) t t'
eqRSort m (RAllT _ t) t'
  = eqRSort m t t'
eqRSort m t (RAllT _ t')
  = eqRSort m t t'
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

eqpd :: Predicate -> Predicate -> Bool
eqpd (Pr vs) (Pr ws)
  = and $ (length vs' == length ws') : [v == w | (v, w) <- zip vs' ws']
    where vs' = sort vs
          ws' = sort ws


instance Eq RTyVar where
  -- FIXME: need to compare unique and string because we reuse
  -- uniques in stringTyVar and co.
  RTV α == RTV α' = α == α' && getOccName α == getOccName α'

instance Ord RTyVar where
  compare (RTV α) (RTV α') = case compare α α' of
    EQ -> compare (getOccName α) (getOccName α')
    o  -> o

instance Hashable RTyVar where
  hashWithSalt i (RTV α) = hashWithSalt i α

instance Ord RTyCon where
  compare x y = compare (rtc_tc x) (rtc_tc y)

instance Hashable RTyCon where
  hashWithSalt i = hashWithSalt i . rtc_tc

--------------------------------------------------------------------
---------------------- Helper Functions ----------------------------
--------------------------------------------------------------------

rVar :: Monoid r => TyVar -> RType c RTyVar r
rVar        = (`RVar` mempty) . RTV

rTyVar :: TyVar -> RTyVar
rTyVar      = RTV


updateRTVar :: Monoid r => RTVar RTyVar i -> RTVar RTyVar (RType RTyCon RTyVar r)
updateRTVar (RTVar (RTV a) _) = RTVar (RTV a) (rTVarInfo a)


rTVar :: Monoid r => TyVar -> RTVar RTyVar (RType RTyCon RTyVar r)
rTVar a = RTVar (RTV a) (rTVarInfo a)
  where

rTVarInfo :: Monoid r => TyVar -> RTVInfo (RType RTyCon RTyVar r) 
rTVarInfo a = RTVInfo { rtv_name   = symbol $ varName a 
                      , rtv_kind   = kindToRType $ tyVarKind a
                      , rtv_is_val = isValKind $ tyVarKind a 
                      }


kindToRType :: Monoid r => Type -> RType RTyCon RTyVar r 
kindToRType = ofType . go
  where
    go t 
     | t == typeSymbolKind = stringTy
     | t == typeNatKind    = intTy
     | otherwise           = t 

isValKind :: Kind -> Bool 
isValKind x = x == typeNatKind || x == typeSymbolKind

bTyVar :: Symbol -> BTyVar
bTyVar      = BTV

symbolRTyVar :: Symbol -> RTyVar
symbolRTyVar = rTyVar . stringTyVar . symbolString

bareRTyVar :: BTyVar -> RTyVar
bareRTyVar (BTV tv) = symbolRTyVar tv

normalizePds :: (OkRT c tv r) => RType c tv r -> RType c tv r
normalizePds t = addPds ps t'
  where
    (t', ps)   = nlzP [] t

rPred :: PVar (RType c tv ()) -> RType c tv r -> RType c tv r
rPred     = RAllP

rEx :: Foldable t
    => t (Symbol, RType c tv r) -> RType c tv r -> RType c tv r
rEx xts t = foldr (\(x, tx) t -> REx x tx t) t xts

rApp :: TyCon
     -> [RType RTyCon tv r]
     -> [RTProp RTyCon tv r]
     -> r
     -> RType RTyCon tv r
rApp c    = RApp (RTyCon c [] (mkTyConInfo c [] [] Nothing))

--- NV TODO : remove this code!!!

addPds :: Foldable t
       => t (PVar (RType c tv ())) -> RType c tv r -> RType c tv r
addPds ps (RAllT v t) = RAllT v $ addPds ps t
addPds ps t           = foldl' (flip rPred) t ps

nlzP :: (OkRT c tv r) => [PVar (RType c tv ())] -> RType c tv r -> (RType c tv r, [PVar (RType c tv ())])
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
 = panic Nothing $ "RefType.nlzP: cannot handle " ++ show t

strengthenRefTypeGen, strengthenRefType ::
         (  OkRT c tv r
         , FreeVar c tv
         , SubsTy tv (RType c tv ()) (RType c tv ())
         , SubsTy tv (RType c tv ()) c
         , SubsTy tv (RType c tv ()) r
         , SubsTy tv (RType c tv ()) tv
         , SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ()))
         ) => RType c tv r -> RType c tv r -> RType c tv r

strengthenRefType_ ::
         ( OkRT c tv r
         , FreeVar c tv
         , SubsTy tv (RType c tv ()) (RType c tv ())
         , SubsTy tv (RType c tv ()) c
         , SubsTy tv (RType c tv ()) r
         , SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ()))
         , SubsTy tv (RType c tv ()) tv
         ) => (RType c tv r -> RType c tv r -> RType c tv r)
           ->  RType c tv r -> RType c tv r -> RType c tv r

strengthenRefTypeGen t1 t2 = strengthenRefType_ f t1 t2
  where
    f (RVar v1 r1) t  = RVar v1 (r1 `meet` fromMaybe mempty (stripRTypeBase t))
    f t (RVar v1 r1)  = RVar v1 (r1 `meet` fromMaybe mempty (stripRTypeBase t))
    f t1 t2           = panic Nothing $ printf "strengthenRefTypeGen on differently shaped types \nt1 = %s [shape = %s]\nt2 = %s [shape = %s]"
                         (pprt_raw t1) (showpp (toRSort t1)) (pprt_raw t2) (showpp (toRSort t2))

pprt_raw :: (OkRT c tv r) => RType c tv r -> String
pprt_raw = render . rtypeDoc Full

-- NEWISH: with unifying type variables: causes big problems with TUPLES?
--strengthenRefType t1 t2 = maybe (errorstar msg) (strengthenRefType_ t1) (unifyShape t1 t2)
--  where msg = printf "strengthen on differently shaped reftypes \nt1 = %s [shape = %s]\nt2 = %s [shape = %s]"
--                 (render t1) (render (toRSort t1)) (render t2) (render (toRSort t2))

-- OLD: without unifying type variables, but checking α-equivalence
strengthenRefType t1 t2
  | meetable t1 t2
  = strengthenRefType_ (\x _ -> x) t1 t2
  | otherwise
  = panic Nothing msg
  where
    msg       = printf "strengthen on differently shaped reftypes \nt1 = %s [shape = %s]\nt2 = %s [shape = %s]"
                  (showpp t1) (showpp (toRSort t1)) (showpp t2) (showpp (toRSort t2))

meetable :: (OkRT c tv r) => RType c tv r -> RType c tv r -> Bool
meetable t1 t2 = toRSort t1 == toRSort t2

strengthenRefType_ f (RAllT a1 t1) (RAllT a2 t2)
  = RAllT a1 $ strengthenRefType_ f t1 (subsTyVar_meet (ty_var_value a2, toRSort t, t) t2)
  where t = RVar (ty_var_value a1) mempty

strengthenRefType_ f (RAllT a t1) t2
  = RAllT a $ strengthenRefType_ f t1 t2

strengthenRefType_ f t1 (RAllT a t2)
  = RAllT a $ strengthenRefType_ f t1 t2

strengthenRefType_ f (RAllP p1 t1) (RAllP _ t2)
  = RAllP p1 $ strengthenRefType_ f t1 t2

strengthenRefType_ f (RAllP p t1) t2
  = RAllP p $ strengthenRefType_ f t1 t2

strengthenRefType_ f t1 (RAllP p t2)
  = RAllP p $ strengthenRefType_ f t1 t2

strengthenRefType_ f (RAllS s t1) t2
  = RAllS s $ strengthenRefType_ f t1 t2

strengthenRefType_ f t1 (RAllS s t2)
  = RAllS s $ strengthenRefType_ f t1 t2

strengthenRefType_ f (RAllE x tx t1) (RAllE y ty t2) | x == y
  = RAllE x (strengthenRefType_ f tx ty) $ strengthenRefType_ f t1 t2

strengthenRefType_ f (RAllE x tx t1) t2
  = RAllE x tx $ strengthenRefType_ f t1 t2

strengthenRefType_ f t1 (RAllE x tx t2)
  = RAllE x tx $ strengthenRefType_ f t1 t2

strengthenRefType_ f (RAppTy t1 t1' r1) (RAppTy t2 t2' r2)
  = RAppTy t t' (r1 `meet` r2)
    where t  = strengthenRefType_ f t1 t2
          t' = strengthenRefType_ f t1' t2'

strengthenRefType_ f (RFun x1 t1 t1' r1) (RFun x2 t2 t2' r2)
  = RFun x2 t t' (r1 `meet` r2)
    where t  = strengthenRefType_ f t1 t2
          t' = strengthenRefType_ f (subst1 t1' (x1, EVar x2)) t2'

strengthenRefType_ f (RApp tid t1s rs1 r1) (RApp _ t2s rs2 r2)
  = RApp tid ts rs (r1 `meet` r2)
    where ts  = zipWith (strengthenRefType_ f) t1s t2s
          rs  = meets rs1 rs2


strengthenRefType_ _ (RVar v1 r1)  (RVar v2 r2) | v1 == v2
  = RVar v1 (r1 `meet` r2)
strengthenRefType_ f t1 t2
  = f t1 t2

meets :: (F.Reftable r) => [r] -> [r] -> [r]
meets [] rs                 = rs
meets rs []                 = rs
meets rs rs'
  | length rs == length rs' = zipWith meet rs rs'
  | otherwise               = panic Nothing "meets: unbalanced rs"


strengthen :: Reftable r => RType c tv r -> r -> RType c tv r
strengthen (RApp c ts rs r) r'  = RApp c ts rs (r `meet` r')
strengthen (RVar a r) r'        = RVar a       (r `meet` r')
strengthen (RFun b t1 t2 r) r'  = RFun b t1 t2 (r `meet` r')
strengthen (RAppTy t1 t2 r) r'  = RAppTy t1 t2 (r `meet` r')
strengthen t _                  = t


quantifyRTy :: Eq tv => [RTVar tv (RType c tv ())] -> RType c tv r -> RType c tv r
quantifyRTy tvs ty = foldr RAllT ty tvs

quantifyFreeRTy :: Eq tv => RType c tv r -> RType c tv r
quantifyFreeRTy ty = quantifyRTy (freeTyVars ty) ty


-------------------------------------------------------------------------
addTyConInfo :: (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r)
             => (M.HashMap TyCon FTycon)
             -> (M.HashMap TyCon RTyCon)
             -> RRType r
             -> RRType r
-------------------------------------------------------------------------
addTyConInfo tce tyi = mapBot (expandRApp tce tyi)

-------------------------------------------------------------------------
expandRApp :: (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r)
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
    fVs                        = tyConTyVarsDef $ rtc_tc rc
    as                         = choosen n ts (rVar <$> fVs)

    choosen 0 _ _           = []
    choosen i (x:xs) (_:ys) = x:choosen (i-1) xs ys
    choosen i []     (y:ys) = y:choosen (i-1) [] ys
    choosen _ _ _           = impossible Nothing "choosen: this cannot happen"

expandRApp _ _ t               = t

rtPropTop
  :: (OkRT c tv r,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv, 
      SubsTy tv (RType c tv ()) tv,
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
   => PVar (RType c tv ()) -> Ref (RType c tv ()) (RType c tv r)
rtPropTop pv = case ptype pv of
                 PVProp t -> RProp xts $ ofRSort t
                 PVHProp  -> RProp xts $ mempty
               where
                 xts      =  pvArgs pv

rtPropPV :: (Fixpoint a, Reftable r)
         => a
         -> [PVar (RType c tv ())]
         -> [Ref (RType c tv ()) (RType c tv r)]
         -> [Ref (RType c tv ()) (RType c tv r)]
rtPropPV rc = safeZipWith msg mkRTProp
  where
    msg     = "appRefts: " ++ showFix rc

mkRTProp :: Reftable r
         => PVar (RType c tv ())
         -> Ref (RType c tv ()) (RType c tv r)
         -> Ref (RType c tv ()) (RType c tv r)
mkRTProp pv (RProp ss (RHole r))
  = RProp ss $ (ofRSort $ pvType pv) `strengthen` r

mkRTProp pv (RProp ss t)
  | length (pargs pv) == length ss
  = RProp ss t
  | otherwise
  = RProp (pvArgs pv) t

pvArgs :: PVar t -> [(Symbol, t)]
pvArgs pv = [(s, t) | (t, s, _) <- pargs pv]


appRTyCon :: SubsTy RTyVar (RType c RTyVar ()) RPVar
          => M.HashMap TyCon FTycon
          -> M.HashMap TyCon RTyCon -> RTyCon -> [RType c RTyVar r] -> RTyCon
appRTyCon tce tyi rc ts = RTyCon c ps' (rtc_info rc'')
  where
    c    = rtc_tc rc
    ps'  = subts (zip (RTV <$> αs) ts') <$> rTyConPVs rc'
    ts'  = if null ts then rVar <$> βs else toRSort <$> ts
    rc'  = M.lookupDefault rc c tyi
    αs   = tyConTyVarsDef $ rtc_tc rc'
    βs   = tyConTyVarsDef c
    rc'' = if isNumeric tce rc' then addNumSizeFun rc' else rc'


-- RJ: The code of `isNumeric` is incomprehensible.
-- Please fix it to use intSort instead of intFTyCon
isNumeric :: M.HashMap TyCon FTycon -> RTyCon -> Bool
isNumeric tce c
  =  fromMaybe
       (symbolFTycon . dummyLoc $ tyConName (rtc_tc c))
       (M.lookup (rtc_tc c) tce) == F.intFTyCon

addNumSizeFun :: RTyCon -> RTyCon
addNumSizeFun c
  = c {rtc_info = (rtc_info c) {sizeFunction = Just EVar} }


generalize :: (Eq tv) => RType c tv r -> RType c tv r
generalize t = mkUnivs (freeTyVars t) [] [] t

freeTyVars :: Eq tv => RType c tv r -> [RTVar tv (RType c tv ())]
freeTyVars (RAllP _ t)     = freeTyVars t
freeTyVars (RAllS _ t)     = freeTyVars t
freeTyVars (RAllT α t)     = freeTyVars t L.\\ [α]
freeTyVars (RFun _ t t' _) = freeTyVars t `L.union` freeTyVars t'
freeTyVars (RApp _ ts _ _) = L.nub $ concatMap freeTyVars ts
freeTyVars (RVar α _)      = [makeRTVar α]
freeTyVars (RAllE _ tx t)  = freeTyVars tx `L.union` freeTyVars t
freeTyVars (REx _ tx t)    = freeTyVars tx `L.union` freeTyVars t
freeTyVars (RExprArg _)    = []
freeTyVars (RAppTy t t' _) = freeTyVars t `L.union` freeTyVars t'
freeTyVars (RHole _)       = []
freeTyVars (RRTy e _ _ t)  = L.nub $ concatMap freeTyVars (t:(snd <$> e))


tyClasses :: (OkRT RTyCon tv r) => RType RTyCon tv r -> [(Class, [RType RTyCon tv r])]
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
tyClasses t               = panic Nothing ("RefType.tyClasses cannot handle" ++ show t)


--------------------------------------------------------------------------------
-- TODO: Rewrite subsTyvars with Traversable
--------------------------------------------------------------------------------

subsTyVars_meet
  :: (Eq tv, Foldable t, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv, 
      SubsTy tv (RType c tv ()) tv, 
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => t (tv, RType c tv (), RType c tv r) -> RType c tv r -> RType c tv r
subsTyVars_meet        = subsTyVars True

subsTyVars_nomeet
  :: (Eq tv, Foldable t, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv, 
      SubsTy tv (RType c tv ()) tv, 
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => t (tv, RType c tv (), RType c tv r) -> RType c tv r -> RType c tv r
subsTyVars_nomeet      = subsTyVars False

subsTyVar_nomeet
  :: (Eq tv, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv, 
      SubsTy tv (RType c tv ()) tv, 
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => (tv, RType c tv (), RType c tv r) -> RType c tv r -> RType c tv r
subsTyVar_nomeet       = subsTyVar False

subsTyVar_meet
  :: (Eq tv, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv, 
      SubsTy tv (RType c tv ()) tv, 
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => (tv, RType c tv (), RType c tv r) -> RType c tv r -> RType c tv r
subsTyVar_meet         = subsTyVar True

subsTyVar_meet'
  :: (Eq tv, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv, 
      SubsTy tv (RType c tv ()) tv, 
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => (tv, RType c tv r) -> RType c tv r -> RType c tv r
subsTyVar_meet' (α, t) = subsTyVar_meet (α, toRSort t, t)

subsTyVars
  :: (Eq tv, Foldable t, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv, 
      SubsTy tv (RType c tv ()) tv, 
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => Bool
  -> t (tv, RType c tv (), RType c tv r)
  -> RType c tv r
  -> RType c tv r
subsTyVars meet ats t = foldl' (flip (subsTyVar meet)) t ats

subsTyVar
  :: (Eq tv, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv, 
      SubsTy tv (RType c tv ()) tv, 
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => Bool
  -> (tv, RType c tv (), RType c tv r)
  -> RType c tv r
  -> RType c tv r
subsTyVar meet        = subsFree meet S.empty

subsFree
  :: (Eq tv, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv, 
      SubsTy tv (RType c tv ()) tv, 
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => Bool
  -> S.HashSet tv 
  -> (tv, RType c tv (), RType c tv r)
  -> RType c tv r
  -> RType c tv r
subsFree m s z (RAllS l t)
  = RAllS l (subsFree m s z t)
subsFree m s z@(α, τ,_) (RAllP π t)
  = RAllP (subt (α, τ) π) (subsFree m s z t)
subsFree m s z@(a, τ, _) (RAllT α t)
  -- subt inside the type variable instantiates the kind of the variable
  = RAllT (subt (a, τ) α) $ subsFree m (ty_var_value α `S.insert` s) z t
subsFree m s z@(α, τ, _) (RFun x t t' r)
  = RFun x (subsFree m s z t) (subsFree m s z t') (subt (α, τ) r)
subsFree m s z@(α, τ, _) (RApp c ts rs r)
  = RApp (subt z' c) (subsFree m s z <$> ts) (subsFreeRef m s z <$> rs) (subt (α, τ) r)
    where z' = (α, τ) -- UNIFY: why instantiating INSIDE parameters?
subsFree meet s (α', τ, t') (RVar α r)
  | α == α' && not (α `S.member` s)
  = if meet then t' `strengthen` (subt (α, τ) r) else t'
  | otherwise
  = RVar (subt (α', τ) α) r
subsFree m s z (RAllE x t t')
  = RAllE x (subsFree m s z t) (subsFree m s z t')
subsFree m s z (REx x t t')
  = REx x (subsFree m s z t) (subsFree m s z t')
subsFree m s z@(α, τ, _) (RAppTy t t' r)
  = subsFreeRAppTy m s (subsFree m s z t) (subsFree m s z t') (subt (α, τ) r)
subsFree _ _ _ t@(RExprArg _)
  = t
subsFree m s z@(α, τ, _) (RRTy e r o t)
  = RRTy (mapSnd (subsFree m s z) <$> e) (subt (α, τ) r) o (subsFree m s z t)
subsFree _ _ (α, τ, _) (RHole r)
  = RHole (subt (α, τ) r)

subsFrees
  :: (Eq tv, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv, 
      SubsTy tv (RType c tv ()) tv, 
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => Bool
  -> S.HashSet tv 
  -> [(tv, RType c tv (), RType c tv r)]
  -> RType c tv r
  -> RType c tv r
subsFrees m s zs t = foldl' (flip (subsFree m s)) t zs

-- GHC INVARIANT: RApp is Type Application to something other than TYCon
subsFreeRAppTy
  :: (Eq tv, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), 
      FreeVar c tv, 
      SubsTy tv (RType c tv ()) tv, 
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => Bool
  -> S.HashSet tv 
  -> RType c tv r
  -> RType c tv r
  -> r
  -> RType c tv r
subsFreeRAppTy m s (RApp c ts rs r) t' r'
  = mkRApp m s c (ts ++ [t']) rs r r'
subsFreeRAppTy _ _ t t' r'
  = RAppTy t t' r'

mkRApp
  :: (Eq tv, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv, 
      SubsTy tv (RType c tv ()) tv, 
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => Bool
  -> S.HashSet tv 
  -> c
  -> [RType c tv r]
  -> [RTProp c tv r]
  -> r
  -> r
  -> RType c tv r
mkRApp m s c ts rs r r'
  | isFun c, [t1, t2] <- ts
  = RFun dummySymbol t1 t2 $ refAppTyToFun r'
  | otherwise
  = subsFrees m s zs $ RApp c ts rs $ r `meet` r' -- (refAppTyToApp r')
  where
    zs = [(tv, toRSort t, t) | (tv, t) <- zip (freeVars c) ts]

refAppTyToFun :: Reftable r => r -> r
refAppTyToFun r
  | isTauto r = r
  | otherwise = panic Nothing "RefType.refAppTyToFun"

subsFreeRef
  :: (Eq tv, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv, 
      SubsTy tv (RType c tv ()) tv, 
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => Bool
  -> S.HashSet tv 
  -> (tv, RType c tv (), RType c tv r)
  -> RTProp c tv r
  -> RTProp c tv r
subsFreeRef _ _ (α', τ', _) (RProp ss (RHole r))
  = RProp (mapSnd (subt (α', τ')) <$> ss) (RHole r)
subsFreeRef m s (α', τ', t')  (RProp ss t)
  = RProp (mapSnd (subt (α', τ')) <$> ss) $ subsFree m s (α', τ', fmap top t') t


-------------------------------------------------------------------
------------------- Type Substitutions ----------------------------
-------------------------------------------------------------------

subts :: (Foldable t, SubsTy tv ty c) => t (tv, ty) -> c -> c
subts = flip (foldr subt)

instance SubsTy RTyVar (RType RTyCon RTyVar ()) RTyVar where
  subt (RTV x, t) (RTV z) | isTyVar z, tyVarKind z == TyVarTy x
    = RTV (setVarType z $ toType t)
  subt _ v 
    = v 

instance SubsTy RTyVar (RType RTyCon RTyVar ()) (RTVar RTyVar (RType RTyCon RTyVar ())) where
  -- NV TODO: update kind 
  subt su rty = rty { ty_var_value = subt su $ ty_var_value rty } 


instance SubsTy BTyVar (RType c BTyVar ()) BTyVar where
  subt _ = id 

instance SubsTy BTyVar (RType c BTyVar ()) (RTVar BTyVar (RType c BTyVar ())) where
  subt _ = id 

instance SubsTy tv ty ()   where
  subt _ = id

instance SubsTy tv ty Symbol where
  subt _ = id



instance (SubsTy tv ty Expr) => SubsTy tv ty Reft where
  subt su (Reft (x, e)) = Reft (x, subt su e)


instance (SubsTy tv ty Sort) => SubsTy tv ty Expr where
  subt su (ELam (x, s) e) = ELam (x, subt su s) $ subt su e
  subt su (EApp e1 e2)    = EApp (subt su e1) (subt su e2)
  subt su (ENeg e)        = ENeg (subt su e)
  subt su (PNot e)        = PNot (subt su e)
  subt su (EBin b e1 e2)  = EBin b (subt su e1) (subt su e2)
  subt su (EIte e e1 e2)  = EIte (subt su e) (subt su e1) (subt su e2)
  subt su (ECst e s)      = ECst (subt su e) (subt su s)
  subt su (ETApp e s)     = ETApp (subt su e) (subt su s)
  subt su (ETAbs e x)     = ETAbs (subt su e) x
  subt su (PAnd es)       = PAnd (subt su <$> es)
  subt su (POr  es)       = POr  (subt su <$> es)
  subt su (PImp e1 e2)    = PImp (subt su e1) (subt su e2)
  subt su (PIff e1 e2)    = PIff (subt su e1) (subt su e2)
  subt su (PAtom b e1 e2) = PAtom b (subt su e1) (subt su e2)
  subt su (PAll xes e)    = PAll (subt su <$> xes) (subt su e)
  subt su (PExist xes e)  = PExist (subt su <$> xes) (subt su e)
  subt _ e                = e

instance (SubsTy tv ty a, SubsTy tv ty b) => SubsTy tv ty (a, b) where
  subt su (x, y) = (subt su x, subt su y)

instance SubsTy BTyVar (RType BTyCon BTyVar ()) Sort where
  subt (v, RVar α _) (FObj s)
    | symbol v == s = FObj $ symbol α
    | otherwise     = FObj s
  subt _ s          = s


instance SubsTy Symbol RSort Sort where
  subt (v, RVar α _) (FObj s)
    | symbol v == s = FObj $ rTyVarSymbol α
    | otherwise     = FObj s
  subt _ s          = s


instance SubsTy RTyVar RSort Sort where
  subt (v, sv) (FObj s)
    | rtyVarUniqueSymbol v == s 
    || symbol v == s 
    = typeSort M.empty $ toType sv 
       -- FObj $ rTyVarSymbol α
    | otherwise     
    = FObj s
  subt _ s         
    = s

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

instance SubsTy TyVar Type SpecType where
  subt (α, τ) = subsTyVar_meet (RTV α, ofType τ, ofType τ)

instance SubsTy RTyVar RTyVar SpecType where
  subt (α, a) = subt (α, RVar a () :: RSort)


instance SubsTy RTyVar RSort RSort where
  subt (α, τ) = subsTyVar_meet (α, τ, ofRSort τ)

instance SubsTy tv RSort Predicate where
  subt _ = id -- NV TODO

instance (SubsTy tv ty r) => SubsTy tv ty (UReft r) where
  subt su r = r {ur_reft = subt su $ ur_reft r}

-- Here the "String" is a Bare-TyCon. TODO: wrap in newtype
instance SubsTy BTyVar BSort BTyCon where
  subt _ t = t

instance SubsTy BTyVar BSort BSort where
  subt (α, τ) = subsTyVar_meet (α, τ, ofRSort τ)

instance (SubsTy tv ty (UReft r), SubsTy tv ty (RType c tv ())) => SubsTy tv ty (RTProp c tv (UReft r))  where
  subt m (RProp ss (RHole p)) = RProp ((mapSnd (subt m)) <$> ss) $ RHole $ subt m p
  subt m (RProp ss t) = RProp ((mapSnd (subt m)) <$> ss) $ fmap (subt m) t

subvUReft     :: (UsedPVar -> UsedPVar) -> UReft Reft -> UReft Reft
subvUReft f (MkUReft r p s) = MkUReft r (subvPredicate f p) s

subvPredicate :: (UsedPVar -> UsedPVar) -> Predicate -> Predicate
subvPredicate f (Pr pvs) = Pr (f <$> pvs)

---------------------------------------------------------------

ofType :: Monoid r => Type -> RType RTyCon RTyVar r
ofType = ofType_ . expandTypeSynonyms

ofType_ :: Monoid r => Type -> RType RTyCon RTyVar r
ofType_ (TyVarTy α)
  = rVar α
ofType_ (FunTy τ τ')
  = rFun dummySymbol (ofType_ τ) (ofType_ τ')
ofType_ (ForAllTy α τ)
  = RAllT (rTVar α) $ ofType_ τ
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

--------------------------------------------------------------------------------
-- | Converting to Fixpoint ----------------------------------------------------
--------------------------------------------------------------------------------


instance Expression Var where
  expr   = eVar

-- TODO: turn this into a map lookup?
dataConReft ::  DataCon -> [Symbol] -> Reft
dataConReft c []
  | c == trueDataCon
  = predReft $ eProp vv_
  | c == falseDataCon
  = predReft $ PNot $ eProp vv_

dataConReft c [x]
  | c == intDataCon
  = symbolReft x -- OLD (vv_, [RConc (PAtom Eq (EVar vv_) (EVar x))])
dataConReft c _
  | not $ isBaseDataCon c
  = mempty
dataConReft c xs
  = exprReft dcValue -- OLD Reft (vv_, [RConc (PAtom Eq (EVar vv_) dcValue)])
  where
    dcValue
      | null xs && null (dataConUnivTyVars c)
      = EVar $ symbol c
      | otherwise
      = mkEApp (dummyLoc $ symbol c) (eVar <$> xs)

isBaseDataCon :: DataCon -> Bool
isBaseDataCon c = and $ isBaseTy <$> dataConOrigArgTys c ++ dataConRepArgTys c

isBaseTy :: Type -> Bool
isBaseTy (TyVarTy _)     = True
isBaseTy (AppTy _ _)     = False
isBaseTy (TyConApp _ ts) = and $ isBaseTy <$> ts
isBaseTy (FunTy _ _)     = False
isBaseTy (ForAllTy _ _)  = False
isBaseTy (LitTy _)       = True


dataConMsReft :: Reftable r => RType c tv r -> [Symbol] -> Reft
dataConMsReft ty ys  = subst su (rTypeReft (ignoreOblig $ ty_res trep))
  where
    trep = toRTypeRep ty
    xs   = ty_binds trep
    ts   = ty_args  trep
    su   = mkSubst $ [(x, EVar y) | ((x, _), y) <- zip (zip xs ts) ys]

---------------------------------------------------------------
---------------------- Embedding RefTypes ---------------------
---------------------------------------------------------------
-- TODO: remove toType, generalize typeSort
toType  :: (Reftable r, PPrint r, SubsTy RTyVar (RType RTyCon RTyVar ()) r) => RRType r -> Type
toType (RFun _ t t' _)
  = FunTy (toType t) (toType t')
toType (RAllT a t) | RTV α <- ty_var_value a 
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
  = impossible Nothing $ "CANNOT HAPPEN: RefType.toType called with: " ++ show t
toType (RRTy _ _ _ t)
  = toType t
toType t
  = impossible Nothing $ "RefType.toType cannot handle: " ++ show t


--------------------------------------------------------------------------------
-- | Annotations and Solutions -------------------------------------------------
--------------------------------------------------------------------------------

rTypeSortedReft ::  (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r) => TCEmb TyCon -> RRType r -> SortedReft
rTypeSortedReft emb t = RR (rTypeSort emb t) (rTypeReft t)

rTypeSort     ::  (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r) => TCEmb TyCon -> RRType r -> Sort
rTypeSort tce = typeSort tce . toType

-------------------------------------------------------------------------------
applySolution :: (Functor f) => FixSolution -> f SpecType -> f SpecType
-------------------------------------------------------------------------------
applySolution = fmap . fmap . mapReft . appSolRefa
  where
    mapReft f (MkUReft (Reft (x, z)) p s) = MkUReft (Reft (x, f z)) p s
-- OLD    appSolRefa _ ra@(RConc _)        = ra
-- OLD    appSolRefa s (RKvar k su)        = RConc $ subst su $ M.lookupDefault PTop k s

appSolRefa :: Visitable t
           => M.HashMap KVar Expr -> t -> t
appSolRefa s p = mapKVars f p
  where
    f k        = Just $ M.lookupDefault PTop k s

-------------------------------------------------------------------------------
shiftVV :: SpecType -> Symbol -> SpecType
-------------------------------------------------------------------------------
shiftVV t@(RApp _ ts rs r) vv'
  = t { rt_args  = subst1 ts (rTypeValueVar t, EVar vv') }
      { rt_pargs = subst1 rs (rTypeValueVar t, EVar vv') }
      { rt_reft  = (`F.shiftVV` vv') <$> r }

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
  show (RTA n as xs t p _) =
    printf "type %s %s %s = %s -- defined at %s" (symbolString n)
      (unwords (show <$> as))
      (unwords (show <$> xs))
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
  = fAppTC (tyConFTyCon tce c) (typeSort tce <$> τs)
typeSort tce (AppTy t1 t2)
  = fApp (typeSort tce t1) [typeSort tce t2]
typeSort _tce (TyVarTy tv)
  = let x = FObj $ tyVarUniqueSymbol tv
    in x
typeSort _ τ
  = FObj $ typeUniqueSymbol τ

tyConFTyCon :: M.HashMap TyCon FTycon -> TyCon -> FTycon
tyConFTyCon tce c    
  = fromMaybe (symbolNumInfoFTyCon (dummyLoc $ tyConName c) (isNumCls c) (isFracCls c)) 
              (M.lookup c tce)

typeSortForAll :: TCEmb TyCon -> Type -> Sort
typeSortForAll tce τ
  = genSort $ typeSort tce tbody
  where genSort t           = foldl (flip FAbs) (sortSubst su t) [0..n-1]
        (as, tbody)         = splitForAllTys τ
        su                  = M.fromList $ zip sas (FVar <$>  [0..])
        sas                 = tyVarUniqueSymbol <$> as
        n                   = length as

tyConName :: TyCon -> Symbol
tyConName c
  | listTyCon == c    = listConName
  | TC.isTupleTyCon c = tupConName
  | otherwise         = let x = symbol c -- . getOccString $ c
                        in x

typeSortFun :: TCEmb TyCon -> Type -> Sort
typeSortFun tce t -- τ1 τ2
  = mkFFunc 0  sos
  where sos  = typeSort tce <$> τs
        τs   = grabArgs [] t

grabArgs :: [Type] -> Type -> [Type]
grabArgs τs (FunTy τ1 τ2)
  | not $ isClassPred τ1 = grabArgs (τ1:τs) τ2
  | otherwise            = grabArgs τs τ2
grabArgs τs τ            = reverse (τ:τs)


mkDataConIdsTy :: (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r)
               => (DataCon, RType RTyCon RTyVar r) -> [(Var, RType RTyCon RTyVar r)]
mkDataConIdsTy (dc, t) = [ expandProductType x t | x <- dataConImplicitIds dc]

expandProductType :: (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r)
                  => Var -> RType RTyCon RTyVar r -> (Var, RType RTyCon RTyVar r)
expandProductType x t
  | ofType (varType x) == toRSort t = (x, t)
  | otherwise                       = (x, t')
     where t'         = fromRTypeRep $ trep {ty_binds = xs', ty_args = ts', ty_refts = rs'}
           τs         = fst $ splitFunTys $ toType t
           trep       = toRTypeRep t
           (xs', ts', rs') = unzip3 $ concatMap mkProductTy $ zip4 τs (ty_binds trep) (ty_args trep) (ty_refts trep)

mkProductTy :: (Monoid t, Monoid r)
            => (Type, Symbol, RType RTyCon RTyVar r, t)
            -> [(Symbol, RType RTyCon RTyVar r, t)]
mkProductTy (τ, x, t, r) = maybe [(x, t, r)] f $ deepSplitProductType_maybe menv τ
  where f    = ((<$>) ((dummySymbol, , mempty) . ofType)) . third4
        menv = (emptyFamInstEnv, emptyFamInstEnv)

-----------------------------------------------------------------------------------------
-- | Binders generated by class predicates, typically for constraining tyvars (e.g. FNum)
-----------------------------------------------------------------------------------------

classBinds :: TyConable c => RType c RTyVar t -> [(Symbol, SortedReft)]
classBinds (RApp c ts _ _)
   | isFracCls c
   = [(rTyVarSymbol a, trueSortedReft FFrac) | (RVar a _) <- ts]
   | isNumCls c
   = [(rTyVarSymbol a, trueSortedReft FNum) | (RVar a _) <- ts]
classBinds _
  = []

rTyVarSymbol :: RTyVar -> Symbol
rTyVarSymbol (RTV α) = typeUniqueSymbol $ TyVarTy α

-----------------------------------------------------------------------------------------
--------------------------- Termination Predicates --------------------------------------
-----------------------------------------------------------------------------------------

makeNumEnv :: (Foldable t, TyConable c) => t (RType c b t1) -> [b]
makeNumEnv = concatMap go
  where
    go (RApp c ts _ _) | isNumCls c || isFracCls c = [ a | (RVar a _) <- ts]
    go _ = []

isDecreasing :: (Eq a, Foldable t1)
             => S.HashSet TyCon -> t1 a -> RType RTyCon a t -> Bool
isDecreasing autoenv  _ (RApp c _ _ _)
  =  isJust (sizeFunction (rtc_info c)) -- user specified size or
  || isSizeable autoenv tc
  where tc = rtc_tc c
isDecreasing _ cenv (RVar v _)
  = v `elem` cenv
isDecreasing _ _ _
  = False

makeDecrType :: Symbolic a
             => S.HashSet TyCon
             -> [(a, (Symbol, RType RTyCon t (UReft Reft)))]
             -> (Symbol, RType RTyCon t (UReft Reft))
makeDecrType autoenv = mkDType autoenv [] []

mkDType :: Symbolic a
        => S.HashSet TyCon
        -> [(Symbol, Symbol, Symbol -> Expr)]
        -> [Expr]
        -> [(a, (Symbol, RType RTyCon t (UReft Reft)))]
        -> (Symbol, RType RTyCon t (UReft Reft))
mkDType autoenv xvs acc [(v, (x, t))]
  = (x, ) $ t `strengthen` tr
  where
    tr = uTop $ Reft (vv, pOr (r:acc))
    r  = cmpLexRef xvs (v', vv, f)
    v' = symbol v
    f  = mkDecrFun autoenv  t
    vv = "vvRec"

mkDType autoenv xvs acc ((v, (x, t)):vxts)
  = mkDType autoenv ((v', x, f):xvs) (r:acc) vxts
  where
    r  = cmpLexRef xvs  (v', x, f)
    v' = symbol v
    f  = mkDecrFun autoenv t


mkDType _ _ _ _
  = panic Nothing "RefType.mkDType called on invalid input"

isSizeable  :: S.HashSet TyCon -> TyCon -> Bool
isSizeable autoenv tc =  S.member tc autoenv --   TC.isAlgTyCon tc -- && TC.isRecursiveTyCon tc

mkDecrFun :: S.HashSet TyCon -> RType RTyCon t t1 -> Symbol -> Expr
mkDecrFun autoenv (RApp c _ _ _)
  | Just f <- sizeFunction $ rtc_info c
  = f
  | isSizeable autoenv $ rtc_tc c
  = \v -> F.mkEApp lenLocSymbol [F.EVar v]
mkDecrFun _ (RVar _ _)
  = EVar
mkDecrFun _ _
  = panic Nothing "RefType.mkDecrFun called on invalid input"

cmpLexRef :: [(t1, t1, t1 -> Expr)] -> (t, t, t -> Expr) -> Expr
cmpLexRef vxs (v, x, g)
  = pAnd $  (PAtom Lt (g x) (g v)) : (PAtom Ge (g x) zero)
         :  [PAtom Eq (f y) (f z) | (y, z, f) <- vxs]
         ++ [PAtom Ge (f y) zero  | (y, _, f) <- vxs]
  where zero = ECon $ I 0

makeLexRefa :: [Located Expr] -> [Located Expr] -> UReft Reft
makeLexRefa es' es = uTop $ Reft (vv, PIff (EVar vv) $ pOr rs)
  where
    rs = makeLexReft [] [] (val <$> es) (val <$> es')
    vv = "vvRec"

makeLexReft :: [(Expr, Expr)] -> [Expr] -> [Expr] -> [Expr] -> [Expr]
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
  = panic Nothing "RefType.makeLexReft on invalid input"

--------------------------------------------------------------------------------
mkTyConInfo :: TyCon -> VarianceInfo -> VarianceInfo -> (Maybe (Symbol -> Expr)) -> TyConInfo
mkTyConInfo c usertyvar userprvariance f
  = TyConInfo (if null usertyvar then defaulttyvar else usertyvar) userprvariance f
  where
        defaulttyvar      = makeTyConVariance c


makeTyConVariance :: TyCon -> VarianceInfo
makeTyConVariance c = varSignToVariance <$> tvs
  where
    tvs = tyConTyVarsDef c

    varsigns = if TC.isTypeSynonymTyCon c
                  then go True (fromJust $ TC.synTyConRhs_maybe c)
                  else L.nub $ concatMap goDCon $ TC.tyConDataCons c

    varSignToVariance v = case filter (\p -> showPpr (fst p) == showPpr v) varsigns of
                            []       -> Invariant
                            [(_, b)] -> if b then Covariant else Contravariant
                            _        -> Bivariant


    goDCon dc = concatMap (go True) (DataCon.dataConOrigArgTys dc)

    go pos (ForAllTy _ t)  = go pos t
    go pos (TyVarTy v)     = [(v, pos)]
    go pos (AppTy t1 t2)   = go pos t1 ++ go pos t2
    go pos (TyConApp c' ts)
       | c == c'
       = []

-- NV fix that: what happens if we have mutually recursive data types?
-- now just provide "default" Bivariant for mutually rec types.
-- but there should be a finer solution
       | mutuallyRecursive c c'
       = concat $ zipWith (goTyConApp pos) (repeat Bivariant) ts
       | otherwise
       = concat $ zipWith (goTyConApp pos) (makeTyConVariance c') ts

    go pos (FunTy t1 t2)   = go (not pos) t1 ++ go pos t2
    go _   (LitTy _)       = []

    goTyConApp _   Invariant     _ = []
    goTyConApp pos Bivariant     t = goTyConApp pos Contravariant t ++ goTyConApp pos Covariant t
    goTyConApp pos Covariant     t = go pos       t
    goTyConApp pos Contravariant t = go (not pos) t

    mutuallyRecursive c c' = c `S.member` (dataConsOfTyCon c')


dataConsOfTyCon :: TyCon -> S.HashSet TyCon
dataConsOfTyCon c = mconcat $ go <$> [t | dc <- TC.tyConDataCons c, t <- DataCon.dataConOrigArgTys dc]
  where
    go (ForAllTy _ t)  = go t
    go (TyVarTy _)     = S.empty
    go (AppTy t1 t2)   = go t1 `S.union` go t2
    go (TyConApp c ts) = S.insert c $ mconcat $ go <$> ts
    go (FunTy t1 t2)   = go t1 `S.union` go t2
    go (LitTy _)       = S.empty

--------------------------------------------------------------------------------
-- | Printing Refinement Types -------------------------------------------------
--------------------------------------------------------------------------------

instance Show RTyVar where
  show = showpp

instance PPrint (UReft r) => Show (UReft r) where
  show = showpp

-- ppHack :: (?callStack :: CallStack) => a -> b
-- ppHack _ = errorstar "OOPS"

instance PPrint (RType c tv r) => Show (RType c tv r) where
  show = showpp

instance PPrint (RTProp c tv r) => Show (RTProp c tv r) where
  show = showpp

instance PPrint REnv where
  pprintTidy k re = "RENV" $+$ pprintTidy k (reLocal re)
