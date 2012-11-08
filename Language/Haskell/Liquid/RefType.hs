{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, ScopedTypeVariables, NoMonomorphismRestriction, FlexibleInstances, UndecidableInstances, TypeSynonymInstances, TupleSections, RankNTypes, GADTs #-}

-- | Refinement Types. Mostly mirroring the GHC Type definition, but with
-- room for refinements of various sorts.

-- TODO: Desperately needs re-organization.
module Language.Haskell.Liquid.RefType (
    RTyVar (..), RType (..), RRType, BRType, RTyCon(..)
  , TyConable (..), Reftable(..), RefTypable (..), SubsTy (..), Ref(..)
  , RTAlias (..)
  , GetPVar (..)
  , BSort, BPVar, BareType, RSort, UsedPVar, RPVar, RReft, RefType
  , PrType, SpecType
  , PVar (..) , Predicate (..), UReft(..), DataDecl (..)

  -- * Functions for lifting Reft-values to Spec-values
  , uTop, uReft, uRType, uRType', uPVar
 
  -- * Functions for manipulating `Predicate`s
  , pdAnd, pdVar, pdTrue, pvars

  -- * Traversing `RType` 
  , ppr_rtype, efoldReft, foldReft, mapReft, mapReftM, mapBot, mapBind
  , freeTyVars, tyClasses

  , ofType, ofPredTree, toType
  , rTyVar, rVar, rApp, rFun
  , expandRApp
  , typeUniqueSymbol
  , strengthen
  , mkArrow, mkUnivs, bkUniv, bkArrow 
  , generalize, normalizePds
  , subts, subvPredicate, subvUReft
  , subsTyVar_meet, subsTyVars_meet, subsTyVar_nomeet, subsTyVars_nomeet
  , stripRTypeBase, rTypeSortedReft, rTypeSort -- , typeSortedReft
  , ofRSort, toRSort
  , varSymbol, dataConSymbol, dataConMsReft, dataConReft  
  , literalRefType, literalReft, literalConst
  -- , primOrderingSort
  , fromRMono, fromRPoly, idRMono
  , isTrivial
  ) where

import GHC
import Outputable
import qualified TyCon as TC
import DataCon
import TypeRep 
import Type (expandTypeSynonyms)

import Var
import Literal
import Type             (isPredTy, substTyWith, classifyPredType, PredTree(..), predTreePredType)
import TysWiredIn       (listTyCon, intDataCon, trueDataCon, falseDataCon) -- , eqDataCon, ltDataCon, gtDataCon)

import Data.Monoid      hiding ((<>))
import Data.Maybe               (fromMaybe)
import Data.Hashable
import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S 
import qualified Data.List as L
import Control.Applicative  hiding (empty)   
import Control.DeepSeq
import Control.Monad  (liftM, liftM2, liftM3)
-- import Data.Generics.Schemes
-- import Data.Generics.Aliases
-- import Data.Data            hiding (TyCon)
import qualified Data.Foldable as Fold
import Text.Printf
-- import Language.Haskell.Liquid.Tidy

import Language.Haskell.Liquid.Fixpoint as F
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.GhcMisc (tracePpr, tvId, intersperse, dropModuleNames, getDataConVarUnique)
import Language.Haskell.Liquid.FileNames (symSepName, listConName, tupConName, boolConName)
import Data.List (sort, isSuffixOf, foldl')

--------------------------------------------------------------------
-- | Predicate Variables -------------------------------------------
--------------------------------------------------------------------

data PVar t
  = PV { pname :: !Symbol
       , ptype :: !t
       , pargs :: ![(t, Symbol, Symbol)]
       }
	deriving (Show) -- (Data, Typeable, Show)

instance Eq (PVar t) where
  pv == pv' = (pname pv == pname pv') {- UNIFY: What about: && eqArgs pv pv' -}

instance Ord (PVar t) where
  compare (PV n _ _)  (PV n' _ _) = compare n n'

instance Functor PVar where
  fmap f (PV x t txys) = PV x (f t) (mapFst3 f <$> txys)

instance (NFData a) => NFData (PVar a) where
  rnf (PV n t txys) = rnf n `seq` rnf t `seq` rnf txys

instance Hashable (PVar a) where
  hash (PV n _ xys) = hash  n -- : (thd3 <$> xys)

--------------------------------------------------------------------
------------------ Predicates --------------------------------------
--------------------------------------------------------------------

type UsedPVar      = PVar ()
newtype Predicate  = Pr [UsedPVar] -- deriving (Data, Typeable) 

pdTrue         = Pr []
pdVar v        = Pr [uPVar v]
pvars (Pr pvs) = pvs
pdAnd ps       = Pr (L.nub $ concatMap pvars ps)

instance Eq Predicate where
  (==) = eqpd

eqpd (Pr vs) (Pr ws) 
  = and $ (length vs' == length ws') : [v == w | (v, w) <- zip vs' ws']
    where vs' = sort vs
          ws' = sort ws

instance Outputable Predicate where
  ppr (Pr [])       = text "True"
  ppr (Pr pvs)      = hsep $ punctuate (text "&") (map ppr pvs)

instance Show Predicate where
  show = showPpr 

instance Reftable Predicate where
  isTauto (Pr ps)      = null ps
  
  ppTy r d | isTauto r = d 
           | otherwise = d <> (angleBrackets $ ppr r)
  
  toReft               = errorstar "TODO: instance of toReft for Predicates. Hmm."


instance NFData Predicate where
  rnf _ = ()

instance NFData r => NFData (UReft r) where
  rnf (U r p) = rnf r `seq` rnf p

instance NFData PrType where
  rnf _ = ()

instance NFData RTyVar where
  rnf _ = ()

--------------------------------------------------------------------
---- Unified Representation of Refinement Types --------------------
--------------------------------------------------------------------

data RType p c tv r
  = RVar { 
      rt_var    :: !tv
    , rt_reft   :: !r 
    }
  
  | RFun  {
      rt_bind   :: !Symbol
    , rt_in     :: !(RType p c tv r)
    , rt_out    :: !(RType p c tv r) 
    , rt_reft   :: !r
    }

  | RAllT { 
      rt_tvbind :: !tv       
    , rt_ty     :: !(RType p c tv r)
    }

  | RAllP {
      rt_pvbind :: !(PVar (RType p c tv ()))
    , rt_ty     :: !(RType p c tv r)
    }

  | RApp  { 
      rt_tycon  :: !c
    , rt_args   :: ![(RType p c tv r)]     
    , rt_pargs  :: ![Ref r (RType p c tv r)] 
    , rt_reft   :: !r
    }

  | RCls  { 
      rt_class  :: !p
    , rt_args   :: ![(RType p c tv r)]
    }

  | REx   { 
      rt_bind   :: !Symbol
    , rt_exarg  :: !(RType p c tv r) 
    , rt_ty     :: !(RType p c tv r) 
    }

  | ROth  !String 
  -- deriving (Data, Typeable)


data Ref s m 
  = RMono s 
  | RPoly m
  -- deriving (Data, Typeable)

data UReft r
  = U { ur_reft :: !r, ur_pred :: !Predicate }
  -- deriving (Data, Typeable)

type BRType     = RType String String String   
type RRType     = RType Class  RTyCon RTyVar   

type BSort      = BRType    ()
type RSort      = RRType    ()

type BPVar      = PVar      BSort
type RPVar      = PVar      RSort

type RReft      = UReft     Reft 
type PrType     = RRType    Predicate
type BareType   = BRType    RReft
type SpecType   = RRType    RReft 
type RefType    = RRType    Reft

-- | Various functions for converting vanilla `Reft` to `Spec`

uRType          ::  RType p c tv a -> RType p c tv (UReft a)
uRType          = fmap uTop 

uRType'         ::  RType p c tv (UReft a) -> RType p c tv a 
uRType'         = fmap ur_reft

uPVar           :: PVar t -> UsedPVar
uPVar           = fmap (const ())

uReft           ::  (Symbol, [Refa]) -> UReft Reft 
uReft           = uTop . Reft  

uTop            ::  r -> UReft r
uTop r          = U r top

--------------------------------------------------------------------
-------------- (Class) Predicates for Valid Refinement Types -------
--------------------------------------------------------------------

class (Monoid r, Subable r, GetPVar r, Outputable r) => Reftable r where 
  isTauto :: r -> Bool
  ppTy    :: r -> SDoc -> SDoc
  
  top     :: r
  top     =  mempty
  
  meet    :: r -> r -> r
  meet    = mappend

  toReft  :: r -> Reft

class (Eq c) => TyConable c where
  isList   :: c -> Bool
  isTuple  :: c -> Bool
  ppTycon  :: c -> SDoc

class ( Outputable p
      , TyConable c
      , Eq p, Eq c, Eq tv
      , Hashable tv
      , Outputable tv
      , Reftable r
      ) => RefTypable p c tv r 
  where
    ppCls    :: p -> [RType p c tv r] -> SDoc
    ppRType  :: Prec -> RType p c tv r -> SDoc 
    -- ppRType  = ppr_rtype True -- False 

-- Monoid Instances ---------------------------------------------------------

instance Monoid Predicate where
  mempty       = pdTrue
  mappend p p' = pdAnd [p, p']

instance (Monoid a) => Monoid (UReft a) where
  mempty                    = U mempty mempty
  mappend (U x y) (U x' y') = U (mappend x x') (mappend y y')


instance ( SubsTy tv (RType p c tv ()) (RType p c tv ())
         , SubsTy tv (RType p c tv ()) c
         , RefTypable p c tv ()
         , RefTypable p c tv r )
        => Monoid (RType p c tv r)  where
  mempty  = error "mempty RefType"
  mappend = strengthenRefType

instance ( SubsTy tv (RType p c tv ()) (RType p c tv ()),
           SubsTy tv (RType p c tv ()) c, 
           Reftable r, 
           RefTypable p c tv (), 
           RefTypable p c tv (UReft r)) 
         => Monoid (Ref r (RType p c tv (UReft r))) where
  mempty                        = RMono mempty
  mappend (RMono r1) (RMono r2) = RMono $ r1 `meet` r2
  mappend (RMono r) (RPoly t)   = RPoly $ t `strengthen` (U r top)
  mappend (RPoly t) (RMono r)   = RPoly $ t `strengthen` (U r top)
  mappend (RPoly t1) (RPoly t2) = RPoly $ t1 `strengthenRefType` t2

instance (Monoid r, Reftable r, RefTypable a b c r) => Monoid (Ref r (RType a b c r)) where
  mempty = RMono mempty
  mappend (RMono r1) (RMono r2) = RMono $ mappend r1 r2
  mappend (RMono r) (RPoly t)   = RPoly $ t `strengthen` r
  mappend (RPoly t) (RMono r)   = RPoly $ t `strengthen` r
  mappend (RPoly t1) (RPoly t2) = RPoly $ t1 `strengthenRefType_` t2

-- Subable Instances ----------------------------------------------

instance Subable () where
  syms _      = []
  subst _ ()  = ()
  substf _ () = ()

instance Subable r => Subable (UReft r) where
  syms (U r p)     = syms r ++ syms p 
  subst s (U r z)  = U (subst s r) (subst s z)
  substf f (U r z) = U (substf f r) (substf f z) 

instance Subable UsedPVar where 
  syms pv         = [ y | (_, x, y) <- pargs pv, x /= y ]
  subst s pv      = pv { pargs = mapThd3 (subst s)  <$> pargs pv }  
  substf f pv     = pv { pargs = mapThd3 (substf f) <$> pargs pv }  

instance Subable Predicate where
  syms (Pr pvs)     = concatMap syms pvs 
  subst s (Pr pvs)  = Pr (subst s <$> pvs)
  substf f (Pr pvs) = Pr (substf f <$> pvs)

instance Subable (Ref F.Reft RefType) where
  syms (RMono r)     = syms r
  syms (RPoly r)     = syms r

  subst su (RMono r) = RMono $ subst su r
  subst su (RPoly r) = RPoly $ subst su r

  substf f (RMono r) = RMono $ substf f r
  substf f (RPoly r) = RPoly $ substf f r

instance Subable r => Subable (RType p c tv r) where
  syms   = foldReft (\r acc -> syms r ++ acc) [] 
  subst  = fmap . subst
  substf = fmap . substf

-- Reftable Instances -------------------------------------------------------

instance Reftable r => Reftable (RType Class RTyCon RTyVar r) where
  isTauto = isTrivial
  ppTy    = errorstar "ppTy RPoly Reftable" 
  toReft  = errorstar "toReft on RType"

instance Reftable Reft where
  isTauto = isTautoReft
  ppTy    = ppr_reft
  toReft  = id

instance Reftable () where
  isTauto _ = True
  ppTy _  d = d
  top       = ()
  meet _ _  = ()
  toReft _  = top

instance (Reftable r) => Reftable (UReft r) where
  isTauto (U r p) = isTauto r && isTauto p 
  ppTy (U r p) d  = ppTy r (ppTy p d) 
  toReft (U r _)  = toReft r

instance (Reftable r, RefTypable p c tv r) => Subable (Ref r (RType p c tv r)) where
  syms (RMono r)     = syms r
  syms (RPoly r)     = syms r

  subst su (RMono r) = RMono (subst su r) 
  subst su (RPoly t) = RPoly (subst su <$> t)

  substf f (RMono r) = RMono (substf f r) 
  substf f (RPoly t) = RPoly (substf f <$> t)

instance (Reftable r, RefTypable p c tv r) => Reftable (Ref r (RType p c tv r)) where
  isTauto (RMono r) = isTauto r
  isTauto (RPoly t) = isTrivial t 
  ppTy (RMono r) d  = ppTy r d
  ppTy (RPoly _) _  = errorstar "Reftable Ref RPoly"
  toReft = error "RefType : toReft"

-- TyConable Instances -------------------------------------------------------

instance TyConable RTyCon where
  isList  = (listTyCon ==) . rTyCon
  isTuple = TC.isTupleTyCon   . rTyCon 
  ppTycon = ppr

instance TyConable String where
  isList  = (listConName ==) 
  isTuple = (tupConName ==)
  ppTycon = text


-- RefTypable Instances -------------------------------------------------------

instance (Eq p, Outputable p, TyConable c, Reftable r) => RefTypable p c String r where
  ppCls = ppClass_String
  ppRType = ppr_rtype True -- False 

instance (Reftable r) => RefTypable Class RTyCon RTyVar r where
  ppCls = ppClass_ClassPred
  ppRType = ppr_rtype True -- False 

  

ppClass_String    c _  = parens (ppr c <+> text "...")
ppClass_ClassPred c ts = parens $ pprClassPred c (toType <$> ts)

-- Eq Instances ------------------------------------------------------

instance (RefTypable p c tv ()) => Eq (RType p c tv ()) where
  (==) = eqRSort M.empty 

eqRSort m (RAllP _ t) (RAllP _ t') 
  = eqRSort m t t'
eqRSort m (RAllP _ t) t' 
  = eqRSort m t t'
eqRSort m (RAllT a t) (RAllT a' t')
  | a == a'
  = eqRSort m t t'
  | otherwise
  = eqRSort (M.insert a' a m) t t' 
-- eqRSort (RAllT (RTV α) t) (RAllT a' t')
  -- = eqRSort t (subt (a', rVar α :: RSort) t') 
eqRSort m (RFun _ t1 t2 _) (RFun _ t1' t2' _) 
  = eqRSort m t1 t1' && eqRSort m t2 t2'
eqRSort m (RApp c ts _ _) (RApp c' ts' _ _)
  =  ((c == c') && length ts == length ts' && and (zipWith (eqRSort m) ts ts'))
eqRSort m (RCls c ts) (RCls c' ts')
  = (c == c') && length ts == length ts' && and (zipWith (eqRSort m) ts ts')
eqRSort m (RVar a _) (RVar a' _)
  = a == (M.lookupDefault a' a' m) 
eqRSort _ _ _ 
  = False

--------------------------------------------------------------------
--------- Wrappers for GHC Type Elements ---------------------------
--------------------------------------------------------------------

newtype RTyVar = RTV TyVar -- deriving (Data, Typeable)

instance Eq RTyVar where
  RTV α == RTV α' = tvId α == tvId α'

instance Ord RTyVar where
  compare (RTV α) (RTV α') = compare (tvId α) (tvId α')

instance Hashable RTyVar where
  hash (RTV α) = hash α


data RTyCon = RTyCon 
  { rTyCon     :: !TC.TyCon         -- GHC Type Constructor
  , rTyConPs   :: ![RPVar]          -- Predicate Parameters
  }
  -- deriving (Data, Typeable)

instance Ord RTyCon where
  compare x y = compare (rTyCon x) (rTyCon y)

instance Eq RTyCon where
  x == y = (rTyCon x) == (rTyCon y)

instance Hashable RTyCon where
  hash   = hash . rTyCon  

--------------------------------------------------------------------
---------------------- Helper Functions ----------------------------
--------------------------------------------------------------------

rFun b t t' = RFun b t t' top

rVar        = (`RVar` top) . RTV 
rTyVar      = RTV

normalizePds t = addPds ps t'
  where (t', ps) = nlzP [] t

rPred p t = RAllP p t
rApp c    = RApp (RTyCon c []) 


addPds ps (RAllT v t) = RAllT v $ addPds ps t
addPds ps t           = foldl' (flip rPred) t ps

nlzP ps t@(RVar _ _ ) 
 = (t, ps)
nlzP ps (RFun b t1 t2 r) 
 = (RFun b t1' t2' r, ps ++ ps1 ++ ps2)
  where (t1', ps1) = nlzP [] t1
        (t2', ps2) = nlzP [] t2
nlzP ps (RAllT v t )
 = (RAllT v t', ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@(RApp _ _ _ _)
 = (t, ps)
nlzP ps t@(RCls _ _)
 = (t, ps)
nlzP ps (RAllP p t)
 = (t', [p] ++ ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@(ROth _)
 = (t, ps)
nlzP ps t@(REx _ _ _) 
 = (t, ps) 


-- NEWISH: with unifying type variables: causes big problems with TUPLES?
--strengthenRefType t1 t2 = maybe (errorstar msg) (strengthenRefType_ t1) (unifyShape t1 t2)
--  where msg = printf "strengthen on differently shaped reftypes \nt1 = %s [shape = %s]\nt2 = %s [shape = %s]" 
--                 (showPpr t1) (showPpr (toRSort t1)) (showPpr t2) (showPpr (toRSort t2))

-- OLD: without unifying type variables, but checking α-equivalence
strengthenRefType t1 t2 
  | eqt t1 t2 
  = strengthenRefType_ t1 t2
  | otherwise
  = errorstar msg 
  where eqt t1 t2 = {- showPpr -} (toRSort t1) == {- showPpr -} (toRSort t2)
        msg = printf "strengthen on differently shaped reftypes \nt1 = %s [shape = %s]\nt2 = %s [shape = %s]" 
                (showPpr t1) (showPpr (toRSort t1)) (showPpr t2) (showPpr (toRSort t2))

unifyShape :: ( RefTypable p c tv r
              , RefTypable p c tv () 
              , SubsTy tv (RType p c tv ()) (RType p c tv ())
              , SubsTy tv (RType p c tv ()) c)
              => RType p c tv r -> RType p c tv r -> Maybe (RType p c tv r)

unifyShape (RAllT a1 t1) (RAllT a2 t2) 
  | a1 == a2      = RAllT a1 <$> unifyShape t1 t2
  | otherwise     = RAllT a1 <$> unifyShape t1 (sub a2 a1 t2)
  where sub a b   = let bt = RVar b top in subsTyVar_meet (a, toRSort bt, bt)

unifyShape t1 t2  
  | eqt t1 t2     = Just t1
  | otherwise     = Nothing
  where eqt t1 t2 = showPpr (toRSort t1) == showPpr (toRSort t2)
         
-- strengthenRefType_ :: RefTypable p c tv r =>RType p c tv r -> RType p c tv r -> RType p c tv r
strengthenRefType_ (RAllT a1 t1) (RAllT _ t2)
  = RAllT a1 $ strengthenRefType_ t1 t2

strengthenRefType_ (RAllP p1 t1) (RAllP _ t2)
  = RAllP p1 $ strengthenRefType_ t1 t2

strengthenRefType_ (RFun x1 t1 t1' r1) (RFun x2 t2 t2' r2) 
  = RFun x1 t t' (r1 `meet` r2)
    where t  = strengthenRefType_ t1 t2
          t' = strengthenRefType_ t1' $ subst1 t2' (x2, EVar x1)

strengthenRefType_ (RApp tid t1s rs1 r1) (RApp _ t2s rs2 r2)
  = RApp tid ts rs (r1 `meet` r2)
    where ts  = zipWith strengthenRefType_ t1s t2s
          rs  = {- tracePpr msg $ -} meets rs1 rs2
          msg = "strengthenRefType_: RApp rs1 = " ++ showPpr rs1 ++ " rs2 = " ++ showPpr rs2


strengthenRefType_ (RVar v1 r1)  (RVar _ r2)
  = RVar v1 ({- tracePpr msg $ -} r1 `meet` r2)
    where msg = "strengthenRefType_: RVAR r1 = " ++ showPpr r1 ++ " r2 = " ++ showPpr r2
 
strengthenRefType_ t1 _ 
  = t1

meets [] rs                 = rs
meets rs []                 = rs
meets rs rs' 
  | length rs == length rs' = zipWith meet rs rs'
  | otherwise               = errorstar "meets: unbalanced rs"


strengthen :: Reftable r => RType p c tv r -> r -> RType p c tv r
strengthen (RApp c ts rs r) r'  = RApp c ts rs (r `meet` r') 
strengthen (RVar a r) r'        = RVar a       (r `meet` r') 
strengthen (RFun b t1 t2 r) r'  = RFun b t1 t2 (r `meet` r')
strengthen t _                  = t 

expandRApp tyi (RApp rc ts rs r)
  = RApp rc' ts (appRefts rc' rs) r
    where rc' = appRTyCon tyi rc ts

expandRApp _ t
  = t

appRTyCon tyi rc@(RTyCon c []) ts = RTyCon c ps'
  where ps' = map (subts (zip (RTV <$> αs) ({- PREDARGS toType -} toRSort <$> ts))) (rTyConPs rc')
        rc' = M.lookupDefault rc c tyi
        αs  = TC.tyConTyVars $ rTyCon rc'
appRTyCon _   (RTyCon c ps) ts = RTyCon c ps'
  where ps' = map (subts (zip (RTV <$> αs) ({- PREDARGS toType -} toRSort <$> ts))) ps
        αs  = TC.tyConTyVars c

appRefts rc [] = RPoly . {- PREDARGS ofType -} ofRSort . ptype <$> (rTyConPs rc)
appRefts rc rs = safeZipWith "appRefts" toPoly rs (ptype <$> (rTyConPs rc))

toPoly (RPoly t) _ = RPoly t
toPoly (RMono r) t = RPoly $ ({- PREDARGS: ofType -} ofRSort t) `strengthen` r  

-- showTy v = showSDoc $ ppr v <> ppr (varUnique v)

mkArrow αs πs xts  = mkUnivs αs πs . mkArrs xts 
  where mkArrs xts t    = foldr (uncurry rFun) t xts 

mkUnivs αs πs t = foldr RAllT (foldr RAllP t πs) αs 

bkUniv :: RType t t1 a t2 -> ([a], [PVar (RType t t1 a ())], RType t t1 a t2)
bkUniv (RAllT α t)      = let (αs, πs, t') = bkUniv t in  (α:αs, πs, t') 
bkUniv (RAllP π t)      = let (αs, πs, t') = bkUniv t in  (αs, π:πs, t') 
bkUniv t                = ([], [], t)

bkArrow (RFun x t t' _) = let (xs, ts, t'') = bkArrow t'  in (x:xs, t:ts, t'')
bkArrow t               = ([], [], t)

-- bkArrs = go []
--   where go xts (RFun x t t' _ ) = go ((x, t) : xts) t'
--         go xts t                = (reverse xts, t)

-- bkUniv = go [] []
--   where go αs πs (RAllT α t)    = go (α : αs) πs t
--         go αs πs (RAllP π t)    = go αs (π : πs) t
--         go αs πs t              = (reverse αs, reverse πs, t)

-- splitVsPs t = go ([], []) t
--   where go (vs, pvs) (RAllT v  t) = go (v:vs, pvs)  t
--         go (vs, pvs) (RAllP pv t) = go (vs, pv:pvs) t
--         go (vs, pvs) t            = (reverse vs, reverse pvs, t)


generalize t = mkUnivs (freeTyVars t) [] t 
         
freeTyVars (RAllP _ t)     = freeTyVars t
freeTyVars (RAllT α t)     = freeTyVars t L.\\ [α]
freeTyVars (RFun _ t t' _) = freeTyVars t `L.union` freeTyVars t' 
freeTyVars (RApp _ ts _ _) = L.nub $ concatMap freeTyVars ts
freeTyVars (RCls _ ts)     = L.nub $ concatMap freeTyVars ts 
freeTyVars (RVar α _)      = [α] 
freeTyVars (REx _ _ t)     = freeTyVars t
freeTyVars (ROth _)        = []

--getTyVars = everything (++) ([] `mkQ` f)
--  where f ((RVar α' _) :: SpecType) = [α'] 
--        f _                         = []

tyClasses (RAllP _ t)     = tyClasses t
tyClasses (RAllT α t)     = tyClasses t
tyClasses (REx _ _ t)     = tyClasses t
tyClasses (RFun _ t t' _) = tyClasses t ++ tyClasses t'
tyClasses (RApp _ ts _ _) = concatMap tyClasses ts 
tyClasses (RCls c ts)     = (c, ts) : concatMap tyClasses ts 
tyClasses (RVar α _)      = [] 
tyClasses (ROth _)        = []



--getTyClasses = everything (++) ([] `mkQ` f)
--  where f ((RCls c ts) :: SpecType) = [(c, ts)]
--        f _                        = []



----------------------------------------------------------------
---------------------- Strictness ------------------------------
----------------------------------------------------------------

instance (NFData a, NFData b) => NFData (Ref a b) where
  rnf (RMono a) = rnf a
  rnf (RPoly b) = rnf b

instance (NFData a, NFData b, NFData c, NFData e) => NFData (RType a b c e) where
  rnf (RVar α r)       = rnf α `seq` rnf r 
  rnf (RAllT α t)      = rnf α `seq` rnf t
  rnf (RAllP π t)      = rnf π `seq` rnf t
  rnf (RFun x t t' r)  = rnf x `seq` rnf t `seq` rnf t' `seq` rnf r
  rnf (RApp _ ts rs r) = rnf ts `seq` rnf rs `seq` rnf r
  rnf (RCls c ts)      = c `seq` rnf ts
  rnf (REx x t t')     = rnf x `seq` rnf t `seq` rnf t'
  rnf (ROth s)         = rnf s

----------------------------------------------------------------
------------------ Printing Refinement Types -------------------
----------------------------------------------------------------

ppr_tyvar = text . tvId

instance Outputable RTyVar where
  ppr (RTV α) = ppr_tyvar α 

instance Show RTyVar where
  show = showPpr 

--instance Reftable (Ref Reft (RType Class RTyCon RTyVar (PVar Type) Reft)) where
--  isTauto (RMono r) = isTauto r
--  isTauto (RPoly t) = isTauto t
--  ppTy (RMono r) = ppTy r
--  ppTy (RPoly t) = ppTy t

-- DEBUG ONLY
--instance Outputable (Bind String (PVar String)) where
--  ppr (RB x) = ppr x
--  ppr (RV a) = text a
--  ppr (RP p) = ppr p
--  
-- instance (Outputable tv, Outputable pv) => Outputable (Bind tv pv) where
--   ppr (RB x) = ppr x
--   ppr (RV a) = ppr a
--   ppr (RP p) = ppr p
-- 
-- instance Outputable (Bind tv pv) => Show (Bind tv pv) where
--   show = showPpr 

instance (Reftable s, Outputable p) => Outputable (Ref s p) where
  ppr (RMono s) = ppr s
  ppr (RPoly p) = ppr p

instance (Reftable r) => Outputable (UReft r) where
  ppr (U r p)
    | isTauto r  = ppr p
    | isTauto p  = ppr r
    | otherwise  = ppr p <> text " & " <> ppr r

instance Outputable (UReft r) => Show (UReft r) where
  show = showSDoc . ppr 

instance Outputable (PVar t) where
  ppr (PV s _ xts) = ppr s <+> hsep (ppr <$> dargs xts)
    where dargs = map thd3 . takeWhile (\(_, x, y) -> x /= y) 
 
-- instance PVarable (PVar Sort) where
--   ppr_def = ppr_pvar_def ppr 

-- instance PVarable (PVar Type) where
--   ppr_def = ppr_pvar_def ppr_pvar_type 

ppr_pvar_def pprv (PV s t xts) = ppr s <+> dcolon <+> intersperse arrow dargs 
  where dargs = [pprv t | (t,_,_) <- xts] ++ [pprv t, text boolConName]

-- ppr_pvar_type (TyVarTy α) = ppr_tyvar α
-- ppr_pvar_type t           = ppr t

instance (RefTypable p c tv r) => Outputable (RType p c tv r) where
  ppr = ppRType TopPrec

instance Outputable (RType p c tv r) => Show (RType p c tv r) where
  show = showSDoc . ppr

instance Outputable RTyCon where
  ppr (RTyCon c _) = ppr c -- <+> text "\n<<" <+> hsep (map ppr ts) <+> text ">>\n"

instance Show RTyCon where
 show = showPpr

ppr_rtype :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> RType p c tv r -> SDoc

ppr_rtype bb p t@(RAllT _ _)       
  = ppr_forall bb p t
ppr_rtype bb p t@(RAllP _ _)       
  = ppr_forall bb p t
ppr_rtype _ _ (RVar a r)         
  = ppTy r $ ppr a
ppr_rtype bb p (RFun x t t' _)  
  = pprArrowChain p $ ppr_dbind bb FunPrec x t : ppr_fun_tail bb t'
ppr_rtype bb p (RApp c [t] rs r)
  | isList c 
  = ppTy r $ brackets (ppr_rtype bb p t) <> ppReftPs bb rs
ppr_rtype bb p (RApp c ts rs r)
  | isTuple c 
  = ppTy r $ parens (intersperse comma (ppr_rtype bb p <$> ts)) <> ppReftPs bb rs
ppr_rtype bb p (RApp c ts rs r)
  = ppTy r $ parens $ ppTycon c <+> ppReftPs bb rs <+> hsep (ppr_rtype bb p <$> ts)
ppr_rtype _ _ (RCls c ts)      
  = ppCls c ts
ppr_rtype bb p t@(REx _ _ _)
  = ppExists bb p t
ppr_rtype _ _ (ROth s)
  = text $ "???-" ++ s 

ppExists :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> RType p c tv r -> SDoc
ppExists bb p t
  = text "exists" <+> brackets (intersperse comma [ppr_dbind bb TopPrec x t | (x, t) <- zs]) <> dot <> ppr_rtype bb p t'
    where (zs,  t')             = split [] t
          split zs (REx x t t') = split ((x,t):zs) t'
          split zs t	        = (reverse zs, t)

ppReftPs bb rs 
  | all isTauto rs = empty
  | not bb         = empty 
  | otherwise      = angleBrackets $ hsep $ punctuate comma $ ppr <$> rs

ppr_dbind :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> Symbol -> RType p c tv r -> SDoc
ppr_dbind bb p x t 
  | isNonSymbol x 
  = ppr_rtype bb p t
  | otherwise
  = ppr x <> colon <> ppr_rtype bb p t

ppr_fun_tail :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> RType p c tv r -> [SDoc]
ppr_fun_tail bb (RFun b t t' _)  
  = (ppr_dbind bb FunPrec b t) : (ppr_fun_tail bb t')
ppr_fun_tail bb t
  = [ppr_rtype bb TopPrec t]

ppr_forall :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> RType p c tv r -> SDoc
ppr_forall b p t
  = maybeParen p FunPrec $ sep [ppr_foralls vs, ppr_rtype b TopPrec t']
  where
    (vs,  t')            = split [] t
    split vs (RAllT α t) = split (Left α : vs) t
    split vs (RAllP π t) = split (Right π : vs) t 
    split vs t	         = (reverse vs, t)
   
ppr_foralls [] = empty
ppr_foralls bs = text "forall" <+> dαs [ α | Left α <- bs] <+> dπs [ π | Right π <- bs] <> dot
  where dαs αs = sep $ ppr <$> αs 
        dπs [] = empty 
        dπs πs = angleBrackets $ intersperse comma $ ppr_pvar_def ppr <$> πs

---------------------------------------------------------------
--------------------------- Visitors --------------------------
---------------------------------------------------------------

-- instance Bifunctor UReft where
--   first f (U r p)  = U (f r) p
--   second f (U r p) = U r (fmap f p)

instance Functor UReft where
  fmap f (U r p) = U (f r) p

instance Functor (RType a b c) where
  fmap  = mapReft 

instance Fold.Foldable (RType a b c) where
  foldr = foldReft

--instance Traversable (RType a b c) where
--  traverse = travReft 




mapReft ::  (r1 -> r2) -> RType p c tv r1 -> RType p c tv r2
mapReft f (RVar α r)          = RVar  α (f r)
mapReft f (RAllT α t)         = RAllT α (mapReft f t)
mapReft f (RAllP π t)         = RAllP π (mapReft f t)
mapReft f (RFun x t t' r)     = RFun  x (mapReft f t) (mapReft f t') (f r)
mapReft f (RApp c ts rs r)    = RApp  c (mapReft f <$> ts) (mapRef f <$> rs) (f r)
mapReft f (RCls c ts)         = RCls  c (mapReft f <$> ts) 
mapReft f (REx z t t')        = REx   z (mapReft f t) (mapReft f t')
mapReft _ (ROth s)            = ROth  s 

mapRef :: (t -> s) -> Ref t (RType p c tv t) -> Ref s (RType p c tv s)
mapRef  f (RMono r)           = RMono $ f r
mapRef  f (RPoly t)           = RPoly $ mapReft f t


------------------------------------------------------------------------------------------------------


mapReftM :: (Monad m) => (r1 -> m r2) -> RType p c tv r1 -> m (RType p c tv r2)
mapReftM f (RVar α r)         = liftM   (RVar  α)   (f r)
mapReftM f (RAllT α t)        = liftM   (RAllT α)   (mapReftM f t)
mapReftM f (RAllP π t)        = liftM   (RAllP π)   (mapReftM f t)
mapReftM f (RFun x t t' r)    = liftM3  (RFun x)    (mapReftM f t)          (mapReftM f t')       (f r)
mapReftM f (RApp c ts rs r)   = liftM3  (RApp  c)   (mapM (mapReftM f) ts)  (mapM (mapRefM f) rs) (f r)
mapReftM f (RCls c ts)        = liftM   (RCls  c)   (mapM (mapReftM f) ts) 
mapReftM f (REx z t t')       = liftM2  (REx z)     (mapReftM f t)          (mapReftM f t')
mapReftM _ (ROth s)           = return  $ ROth  s 


mapRefM  :: (Monad m) => (t -> m s) -> Ref t (RType p c tv t) -> m (Ref s (RType p c tv s))
mapRefM  f (RMono r)          = liftM   RMono       (f r)
mapRefM  f (RPoly t)          = liftM   RPoly       (mapReftM f t)

-- foldReft ::  (r -> a -> a) -> a -> RType p c tv r -> a
foldReft f = efoldReft (\_ -> f) [] 

efoldReft :: ([F.Symbol] -> r -> a -> a) -> [F.Symbol] -> a -> RType p c tv r -> a
efoldReft f γ z (RVar _ r)       = f γ r z 
efoldReft f γ z (RAllT _ t)      = efoldReft f γ z t
efoldReft f γ z (RAllP _ t)      = efoldReft f γ z t
efoldReft f γ z (RFun x t t' r)  = f γ r (efoldReft f (x:γ) (efoldReft f γ z t) t')
efoldReft f γ z (RApp _ ts rs r) = f γ r (efoldRefs f γ (efoldRefts f γ z ts) rs)
efoldReft f γ z (RCls _ ts)      = efoldRefts f γ z ts
efoldReft f γ z (REx _ t t')     = efoldRefts f γ z [t, t']
efoldReft _ _ z (ROth _)         = z 

efoldRefts :: ([Symbol] -> t3 -> c -> c)-> [Symbol] -> c -> [RType t t1 t2 t3] -> c
efoldRefts f γ z ts              = foldr (flip $ efoldReft f γ) z ts 

efoldRefs :: ([Symbol] -> t3 -> c -> c)-> [Symbol] -> c -> [Ref t3 (RType t t1 t2 t3)] -> c
efoldRefs  f γ z rs              = foldr (flip $ efoldRef f γ) z  rs 

efoldRef :: ([Symbol] -> t3 -> c -> c)-> [Symbol] -> c -> Ref t3 (RType t t1 t2 t3) -> c
efoldRef f γ z (RMono r)         = f γ r z
efoldRef f γ z (RPoly t)         = efoldReft f γ z t


isTrivial :: (Functor t, Fold.Foldable t, Reftable a) => t a -> Bool
isTrivial = Fold.and . fmap isTauto

class GetPVar a where
  getUPVars :: a  -> [PVar ()]

instance GetPVar () where
  getUPVars _ = []

instance GetPVar Predicate where
  getUPVars (Pr ps) = ps

instance GetPVar (UReft r) where
  getUPVars (U _ ps) = getUPVars ps

instance GetPVar Refa where
  getUPVars _ = []

instance GetPVar Reft where
  getUPVars _ = []

instance GetPVar r => GetPVar (RType p c tv r) where
  getUPVars = foldReft (\r acc -> getUPVars r ++ acc) [] 

instance GetPVar r => GetPVar (Ref r (RType p c tv r)) where
  getUPVars (RMono r) = getUPVars r
  getUPVars (RPoly t) = getUPVars t

  -- foldReft (\r acc -> getUPVars r ++ acc) [] 


--instance (Data r, Typeable r, GetPVar r) 
--          => GetPVar (RType Class RTyCon RTyVar r) where
--  getUPVars = everything (++) ([] `mkQ` go) 
--    where go (ref :: r) = getUPVars ref
--
--instance (Data r2, Typeable r2, GetPVar r2, GetPVar r1) 
--         => GetPVar (Ref r1 (RType Class RTyCon RTyVar r2)) where
--  getUPVars (RMono r) = getUPVars r
--  getUPVars (RPoly t) = getUPVars t

-- mkTrivial = mapReft (\_ -> ())


------------------------------------------------------------------------------------------
-- TODO: Rewrite subsTyvars with Traversable
------------------------------------------------------------------------------------------

subsTyVars_meet       = subsTyVars True
subsTyVars_nomeet     = subsTyVars False
subsTyVar_nomeet      = subsTyVar False
subsTyVar_meet        = subsTyVar True
subsTyVars meet ats t = foldl' (flip (subsTyVar meet)) t ats
subsTyVar meet        = subsFree' meet S.empty


subsFree' = subsFree 

--subsFree :: ( Ord tv
--            , SubsTy tv ty c
--            , SubsTy tv ty r
--            , SubsTy tv ty (PVar (RType p c tv ()))
--            , RefTypable p c tv r) 
--            => Bool 
--            -> S.Set tv
--            -> (tv, ty, RType p c tv r) 
--            -> RType p c tv r 
--            -> RType p c tv r

subsFree m s z@(α, τ,_) (RAllP π t)         
  = RAllP (subt (α, τ) π) (subsFree m s z t)
subsFree m s z (RAllT α t)         
  = RAllT α $ subsFree m (α `S.insert` s) z t
subsFree m s z@(_, _, _) (RFun x t t' r)       
  = RFun x (subsFree m s z t) (subsFree m s z t') ({- subt (α, τ) -} r)
subsFree m s z@(α, τ, _) (RApp c ts rs r)     
  = RApp (subt z' c) (subsFree m s z <$> ts) (subsFreeRef m s z <$> rs) ({- subt z' -} r)  
    where z' = (α, τ) -- UNIFY: why instantiating INSIDE parameters?
subsFree m s z (RCls c ts)     
  = RCls c (subsFree m s z <$> ts)
subsFree meet s (α', _, t') t@(RVar α r) 
  | α == α' && not (α `S.member` s) 
  = if meet then t' `strengthen` {- subt (α', τ') -} r else t' 
  | otherwise
  = t
subsFree m s z (REx x t t')
  = REx x (subsFree m s z t) (subsFree m s z t')
subsFree _ _ _ t@(ROth _)        
  = t
-- subsFree _ _ _ t      
--   = errorstar $ "subsFree fails on: " ++ showPpr t

-- subsFreeRef ::  (Ord tv, SubsTy tv ty r, SubsTy tv ty (PVar ty), SubsTy tv ty c, Reftable r, Monoid r, Subable r, RefTypable p c tv (PVar ty) r) => Bool -> S.Set tv -> (tv, ty, RType p c tv (PVar ty) r) -> Ref r (RType p c tv (PVar ty) r) -> Ref r (RType p c tv (PVar ty) r)

subsFreeRef m s (α', τ', t')  (RPoly t) 
  = RPoly $ subsFree m s (α', τ', fmap (\_ -> top) t') t
subsFreeRef _ _ (_, _, _) (RMono r) 
  = RMono $ {- subt (α', τ') -} r

mapBot f (RAllT α t)       = RAllT α (mapBot f t)
mapBot f (RAllP π t)       = RAllP π (mapBot f t)
mapBot f (RFun x t t' r)   = RFun x (mapBot f t) (mapBot f t') r
mapBot f (RApp c ts rs r)  = f $ RApp c (mapBot f <$> ts) (mapBotRef f <$> rs) r
mapBot f (RCls c ts)       = RCls c (mapBot f <$> ts)
mapBot f t'                = f t' 
mapBotRef _ (RMono r)      = RMono $ r
mapBotRef f (RPoly t)      = RPoly $ mapBot f t

-------------------------------------------------------------------
------------------- Type Substitutions ----------------------------
-------------------------------------------------------------------

class SubsTy tv ty a where
  subt :: (tv, ty) -> a -> a

subts = flip (foldr subt) 

instance SubsTy tv ty ()   where
  subt _ = id

instance SubsTy tv ty Reft where
  subt _ = id

instance (SubsTy tv ty ty) => SubsTy tv ty (PVar ty) where
  subt su (PV n t xts) = PV n (subt su t) [(subt su t, x, y) | (t,x,y) <- xts] 

instance SubsTy RTyVar RSort RTyCon where  
   subt z c = c {rTyConPs = subt z <$> rTyConPs c}

-- NOTE: This DOES NOT substitute at the binders
instance SubsTy RTyVar RSort PrType where   
  subt (α, τ) = subsTyVar_meet (α, τ, ofRSort τ)

instance SubsTy RTyVar RSort RSort where   
  subt (α, τ) = subsTyVar_meet (α, τ, ofRSort τ)

-- Here the "String" is a Bare-TyCon. TODO: wrap in newtype 
instance SubsTy String BSort String where
  subt _ t = t

instance SubsTy String BSort BSort where
  subt (α, τ) = subsTyVar_meet (α, τ, ofRSort τ)

instance (SubsTy tv ty (UReft r)) => SubsTy tv ty (Ref (UReft r) (RType p c tv (UReft r)))  where
  subt m (RMono p) = RMono $ subt m p
  subt m (RPoly t) = RPoly $ fmap (subt m) t
 
subvUReft     :: (UsedPVar -> UsedPVar) -> UReft Reft -> UReft Reft
subvUReft f (U r p) = U r (subvPredicate f p)

subvPredicate :: (UsedPVar -> UsedPVar) -> Predicate -> Predicate 
subvPredicate f (Pr pvs) = Pr (f <$> pvs)

---------------------------------------------------------------

-- stripRTypeBase ::  RType a -> Maybe a
stripRTypeBase (RApp _ _ _ x)   
  = Just x
stripRTypeBase (RVar _ x)   
  = Just x
stripRTypeBase (RFun _ _ _ x)   
  = Just x
stripRTypeBase _                
  = Nothing


ofType ::  Reftable r => Type -> RRType r
ofType = ofType_ . expandTypeSynonyms 

ofType_ (TyVarTy α)     
  = rVar α
ofType_ (FunTy τ τ')    
  = rFun dummySymbol (ofType_ τ) (ofType_ τ') 
ofType_ (ForAllTy α τ)  
  = RAllT (rTyVar α) $ ofType_ τ  
ofType_ τ
  | isPredTy τ
  = ofPredTree (classifyPredType τ)  
ofType_ (TyConApp c τs)
  | TC.isSynTyCon c
  = ofType_ $ substTyWith αs τs τ
  | otherwise
  = rApp c (ofType_ <$> τs) [] top 
  where (αs, τ) = TC.synTyConDefn c
ofType_ τ               
  = errorstar ("ofType cannot handle: " ++ showPpr τ)

ofPredTree (ClassPred c τs)
  = RCls c (ofType_ <$> τs)
ofPredTree _
  = errorstar "ofPredTree"

----------------------------------------------------------------
------------------- Converting to Fixpoint ---------------------
----------------------------------------------------------------


varSymbol ::  Var -> Symbol
varSymbol v 
  | us `isSuffixOf` vs = stringSymbol vs  
  | otherwise          = stringSymbol $ vs ++ [symSepName] ++ us
  where us  = showPpr $ getDataConVarUnique v
        vs  = pprShort v

pprShort    =  dropModuleNames . showPpr

dataConSymbol ::  DataCon -> Symbol
dataConSymbol = varSymbol . dataConWorkId

-- ordCon s = EDat (dataConSymbol s) primOrderingSort 
-- primOrderingSort = typeSort M.empty $ dataConRepType eqDataCon

-- TODO: turn this into a map lookup?
dataConReft ::  DataCon -> [Symbol] -> Reft
dataConReft c [] 
  | c == trueDataCon
  = Reft (vv, [RConc $ (PBexp (EVar vv))]) 
  | c == falseDataCon
  = Reft (vv, [RConc $ PNot (PBexp (EVar vv))]) 
--  | otherwise
--  = Reft (vv, [RConc $ (PAtom Eq (EVar vv) (EVar (dataConSymbol c)))]) 
--  | c `elem`  [gtDataCon, ltDataCon, eqDataCon]
--  = Reft (vv, [RConc (PAtom Eq (EVar vv) (ordCon c))]) 
dataConReft c [x] 
  | c == intDataCon 
  = Reft (vv, [RConc (PAtom Eq (EVar vv) (EVar x))]) 
dataConReft _ _ 
 = Reft (vv, [RConc PTrue]) 
 
-- dataConReft c xs
--  = Reft (vv, [RConc (PAtom Eq (EVar vv) (EApp (dataConSymbol c) (EVar <$> xs)))]) 
  -- = Reft (vv, [RConc PTrue]) 

dataConMsReft ty ys  = subst su (refTypeReft t) 
  where (xs, ts, t)  = bkArrow $ thd3 $ bkUniv ty    -- bkArrow ty 
        su           = mkSubst [(x, EVar y) | ((x,_), y) <- zip (zip xs ts) ys] 

--bkArrow ty = (αs, πs, xts, out)
--  where (αs, πs, t) = bkUniv ty
--        (xts,  out) = bkArrs t


---------------------------------------------------------------
---------------------- Embedding RefTypes ---------------------
---------------------------------------------------------------

toRSort :: RType p c tv r -> RType p c tv () 
toRSort = stripQuantifiers . mapBind (const dummySymbol) . fmap (const ())

ofRSort ::  Reftable r => RType p c tv () -> RType p c tv r 
ofRSort = fmap (\_ -> top)

stripQuantifiers (RAllT α t)      = RAllT α (stripQuantifiers t)
stripQuantifiers (RAllP _ t)      = stripQuantifiers t
stripQuantifiers (REx _ _ t)      = stripQuantifiers t
stripQuantifiers (RFun x t t' r)  = RFun x (stripQuantifiers t) (stripQuantifiers t') r
stripQuantifiers (RApp c ts rs r) = RApp c (stripQuantifiers <$> ts) (stripQuantifiersRef <$> rs) r
stripQuantifiers (RCls c ts)      = RCls c (stripQuantifiers <$> ts)
stripQuantifiers t                = t
stripQuantifiersRef (RPoly t)     = RPoly $ stripQuantifiers t
stripQuantifiersRef r             = r

-- TODO: remove toType, generalize typeSort 
toType  :: RRType r -> Type
toType (RFun _ t t' _)   
  = FunTy (toType t) (toType t')
toType (RAllT (RTV α) t)      
  = ForAllTy α (toType t)
toType (RAllP _ t)
  = toType t
toType (RVar (RTV α) _)        
  = TyVarTy α
toType (RApp (RTyCon {rTyCon = c}) ts _ _)   
  = TyConApp c (toType <$> ts)
toType (RCls c ts)   
  = predTreePredType $ ClassPred c (toType <$> ts)
toType (REx _ _ t)
  = toType t
toType (ROth _)      
  = errorstar $ "toType fails: ROth "

mapBind f (RAllT α t)      = RAllT α (mapBind f t)
mapBind f (RAllP π t)      = RAllP π (mapBind f t)
mapBind f (RFun b t1 t2 r) = RFun (f b)  (mapBind f t1) (mapBind f t2) r
mapBind f (RApp c ts rs r) = RApp c (mapBind f <$> ts) (mapBindRef f <$> rs) r
mapBind f (RCls c ts)      = RCls c (mapBind f <$> ts)
mapBind f (REx b t1 t2)    = REx  (f b) (mapBind f t1) (mapBind f t2)
mapBind _ (RVar α r)       = RVar α r
mapBind _ (ROth s)         = ROth s

mapBindRef _ (RMono r)     = RMono r
mapBindRef f (RPoly t)     = RPoly $ mapBind f t


---------------------------------------------------------------
----------------------- Typing Literals -----------------------
---------------------------------------------------------------

literalRefType tce l 
  = makeRTypeBase (literalType l) (literalReft tce l) 

-- makeRTypeBase :: Type -> Reft -> RefType 
makeRTypeBase (TyVarTy α)    x       
  = RVar (rTyVar α) x 
makeRTypeBase (TyConApp c _) x 
  = rApp c [] [] x
makeRTypeBase _              _
  = error "RefType : makeRTypeBase"

literalReft tce                = exprReft . snd . literalConst tce 

literalConst tce l             = (sort, mkLit l)
  where sort                   = typeSort tce $ literalType l 
        sym                    = stringSymbol $ "$$" ++ showPpr l
        mkLit (MachInt    n)   = mkI n
        mkLit (MachInt64  n)   = mkI n
        mkLit (MachWord   n)   = mkI n
        mkLit (MachWord64 n)   = mkI n
        mkLit (LitInteger n _) = mkI n
        mkLit _                = ELit sym sort
        mkI                    = ECon . I

---------------------------------------------------------------
---------------- Annotations and Solutions --------------------
---------------------------------------------------------------

rTypeSortedReft       ::  (Reftable r) => TCEmb TyCon -> RRType r -> SortedReft
rTypeSortedReft emb t = RR (rTypeSort emb t) (refTypeReft t)

refTypeReft :: (Reftable r) => RType p c tv r -> Reft
refTypeReft = fromMaybe top . fmap toReft . stripRTypeBase 
-- refTypeReft t = fromMaybe top $ ur_reft <$> stripRTypeBase t

-- typeSortedReft emb t r = RR (typeSort emb t) (Reft (vv, [r]))

rTypeSort     ::  TCEmb TyCon -> RRType r -> Sort
rTypeSort tce = typeSort tce . toType

------------------------------------------------------------------------
---------------- Auxiliary Stuff Used Elsewhere ------------------------
------------------------------------------------------------------------

-- | Data type refinements

data DataDecl   = D String 
                    [String] 
                    [PVar BSort] 
                    [(String, [(String, BareType)])] 
                  deriving (Show) 

-- | Refinement Type Aliases

data RTAlias tv ty 
  = RTA { rtName :: String
        , rtArgs :: [tv]
        , rtBody :: ty              
        } -- deriving (Data, Typeable)

instance (Show tv, Show ty) => Show (RTAlias tv ty) where
  show (RTA n args t) = "reftype " ++ n ++ " " ++ as ++ " = " ++ show t 
                        where as = L.intercalate " " (show <$> args)


-- fromRMono :: String -> Ref a b -> a
fromRMono _ (RMono r) = r
fromRMono msg _       = errorstar $ "fromMono: " ++ msg -- ++ showPpr z
fromRPoly (RPoly r)   = r
fromRPoly _           = errorstar "fromPoly"
idRMono               = RMono . fromRMono "idRMono"

