{-# LANGUAGE IncoherentInstances        #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE FlexibleContexts           #-} 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE PatternGuards              #-}

-- | Refinement Types. Mostly mirroring the GHC Type definition, but with
-- room for refinements of various sorts.

-- TODO: Desperately needs re-organization.
module Language.Haskell.Liquid.RefType (

  -- * Functions for lifting Reft-values to Spec-values
    uTop, uReft, uRType, uRType', uRTypeGen, uPVar
 
  -- * Functions for decreasing arguments
  , isDecreasing, makeDecrType

  -- * Functions for manipulating `Predicate`s
  , pdVar
  -- , pdAnd, pdTrue, pvars
  , findPVar
  , freeTyVars, tyClasses, tyConName

  , ofType, ofPredTree, toType
  , rTyVar, rVar, rApp 
  , expandRApp, appRTyCon
  , typeSort, typeUniqueSymbol
  , strengthen
  , generalize, normalizePds
  , subts, subvPredicate, subvUReft
  , subsTyVar_meet, subsTyVars_meet, subsTyVar_nomeet, subsTyVars_nomeet
  , rTypeSortedReft, rTypeSort
  , varSymbol, dataConSymbol, dataConMsReft, dataConReft  
  , literalFRefType, literalFReft, literalConst
  , mkDataConIdsTy
  , classBinds
  ) where

import Var
import Literal
import GHC
import DataCon
import PrelInfo         (isNumericClass)
import qualified TyCon  as TC
import TypeRep          hiding (maybeParen, pprArrowChain)  
import Type             (splitFunTys, expandTypeSynonyms)
import Type             (isPredTy, substTyWith, classifyPredType, PredTree(..), predTreePredType)
import TysWiredIn       (listTyCon, intDataCon, trueDataCon, falseDataCon)

import Data.Monoid      hiding ((<>))
import Data.Maybe               (fromMaybe, isJust)
import Data.Hashable
import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S 
import qualified Data.List as L
import Control.Applicative  hiding (empty)   
import Control.DeepSeq
import Control.Monad  (liftM, liftM2, liftM3)
import qualified Data.Foldable as Fold
import Text.Printf
import Text.PrettyPrint.HughesPJ
import Text.Parsec.Pos  (SourcePos)

import Language.Haskell.Liquid.PrettyPrint
import Language.Fixpoint.Types hiding (Predicate)
import Language.Haskell.Liquid.Types hiding (DataConP (..))

import Language.Fixpoint.Misc
import Language.Haskell.Liquid.GhcMisc (sDocDoc, typeUniqueString, tracePpr, tvId, getDataConVarUnique, mkTyConInfo, showSDoc, showPpr, showSDocDump)
import Language.Fixpoint.Names (dropModuleNames, symSepName, funConName, listConName, tupConName, propConName, boolConName)
import Data.List (sort, isSuffixOf, foldl')

pdVar v        = Pr [uPVar v]

findPVar :: [PVar (RType p c tv ())] -> UsedPVar -> PVar (RType p c tv ())
findPVar ps p 
  = PV name ty $ zipWith (\(_, _, e) (t, s, _) -> (t, s, e))(pargs p) args
  where PV name ty args = fromMaybe (msg p) $ L.find ((==(pname p)) . pname) ps
        msg p = errorstar $ "RefType.findPVar" ++ showpp p ++ "not found"

-- | Various functions for converting vanilla `Reft` to `Spec`

uRType          ::  RType p c tv a -> RType p c tv (UReft a)
uRType          = fmap uTop 

uRType'         ::  RType p c tv (UReft a) -> RType p c tv a 
uRType'         = fmap ur_reft

uRTypeGen       :: Reftable b => RType p c tv a -> RType p c tv b
uRTypeGen       = fmap (\_ -> top)

uPVar           :: PVar t -> UsedPVar
uPVar           = fmap (const ())

uReft           ::  (Symbol, [Refa]) -> UReft Reft 
uReft           = uTop . Reft  

uTop            ::  r -> UReft r
uTop r          = U r top

--------------------------------------------------------------------
-------------- (Class) Predicates for Valid Refinement Types -------
--------------------------------------------------------------------

-- Monoid Instances ---------------------------------------------------------


instance ( SubsTy tv (RType p c tv ()) (RType p c tv ())
         , SubsTy tv (RType p c tv ()) c
         , RefTypable p c tv ()
         , RefTypable p c tv r 
         , PPrint (RType p c tv r)
         )
        => Monoid (RType p c tv r)  where
  mempty  = error "mempty RefType"
  mappend = strengthenRefType

-- MOVE TO TYPES
instance ( SubsTy tv (RType p c tv ()) (RType p c tv ())
         , SubsTy tv (RType p c tv ()) c
         , Reftable r 
         , RefTypable p c tv ()
         , RefTypable p c tv (UReft r)) 
         => Monoid (Ref (RType p c tv ()) r (RType p c tv (UReft r))) where
  mempty                              = RMono [] mempty
  mappend (RMono s1 r1) (RMono s2 r2) = RMono (s1 ++ s2) $ r1 `meet` r2
  mappend (RMono s1 r) (RPoly s2 t)   = RPoly (s1 ++ s2) $ t  `strengthen` (U r top)
  mappend (RPoly s1 t) (RMono s2 r)   = RPoly (s1 ++ s2) $ t  `strengthen` (U r top)
  mappend (RPoly s1 t1) (RPoly s2 t2) = RPoly (s1 ++ s2) $ t1 `strengthenRefType` t2

instance ( Monoid r, Reftable r
         , RefTypable a b c r
         , RefTypable a b c ()
         ) => Monoid (Ref (RType a b c ()) r (RType a b c r)) where
  mempty                              = RMono [] mempty
  mappend (RMono s1 r1) (RMono s2 r2) = RMono (s1 ++ s2)  $ mappend r1 r2
  mappend (RMono s1 r) (RPoly s2 t)   = RPoly (s1 ++ s2)  $ t `strengthen` r
  mappend (RPoly s1 t) (RMono s2 r)   = RPoly (s1 ++ s2)  $ t `strengthen` r
  mappend (RPoly s1 t1) (RPoly s2 t2) = RPoly (s1 ++ s2)  $ t1 `strengthenRefType_` t2

instance (Reftable r, RefTypable p c tv r, RefTypable p c tv ()) 
         => Reftable (Ref (RType p c tv ()) r (RType p c tv r)) where
  isTauto (RMono _ r) = isTauto r
  isTauto (RPoly _ t) = isTrivial t 
  ppTy (RMono _ r) d  = ppTy r d
  ppTy (RPoly _ _) _  = errorstar "RefType: Reftable ppTy in RPoly"
  toReft              = errorstar "RefType: Reftable toReft"
  params              = errorstar "RefType: Reftable params for Ref"


-- Subable Instances ----------------------------------------------

instance Subable (Ref RSort Reft RefType) where
  syms (RMono ss r)     = (fst <$> ss) ++ syms r
  syms (RPoly ss t)     = (fst <$> ss) ++ syms t

  subst su (RMono ss r) = RMono (mapSnd (subst su) <$> ss) $ subst su r 
  subst su (RPoly ss r) = RPoly (mapSnd (subst su) <$> ss) $ subst su r

  substf f (RMono ss r) = RMono (mapSnd (substf f) <$> ss) $ substf f r
  substf f (RPoly ss r) = RPoly (mapSnd (substf f) <$> ss) $ substf f r
  substa f (RMono ss r) = RMono (mapSnd (substa f) <$> ss) $ substa f r
  substa f (RPoly ss r) = RPoly (mapSnd (substa f) <$> ss) $ substa f r

-- Reftable Instances -------------------------------------------------------

instance (PPrint r, Reftable r) => Reftable (RType Class RTyCon RTyVar r) where
  isTauto     = isTrivial
  ppTy        = errorstar "ppTy RPoly Reftable" 
  toReft      = errorstar "toReft on RType"
  params      = errorstar "params on RType"

-- ppTySReft s r d 
--   = text "\\" <> hsep (toFix <$> s) <+> text "->" <+> ppTy r d



-- MOVE TO TYPES

-- TyConable Instances -------------------------------------------------------

-- MOVE TO TYPES
instance TyConable RTyCon where
  isFun   = isFunTyCon . rTyCon
  isList  = (listTyCon ==) . rTyCon
  isTuple = TC.isTupleTyCon   . rTyCon 
  ppTycon = toFix 

-- MOVE TO TYPES
instance TyConable String where
  isFun   = (funConName ==) 
  isList  = (listConName ==) 
  isTuple = (tupConName ==)
  ppTycon = text


-- RefTypable Instances -------------------------------------------------------

-- MOVE TO TYPES
instance Fixpoint String where
  toFix = text 

-- MOVE TO TYPES
instance Fixpoint Class where
  toFix = text . showPpr

-- MOVE TO TYPES
instance (Eq p, PPrint p, TyConable c, Reftable r, PPrint r) => RefTypable p c String r where
  ppCls   = ppClass_String
  ppRType = ppr_rtype $ ppPs ppEnv
  -- ppBase  = undefined 

-- MOVE TO TYPES
instance (Reftable r, PPrint r) => RefTypable Class RTyCon RTyVar r where
  ppCls   = ppClass_ClassPred
  ppRType = ppr_rtype $ ppPs ppEnv
  -- ppBase  = undefined


-- MOVE TO TYPES
class FreeVar a v where 
  freeVars :: a -> [v]

-- MOVE TO TYPES
instance FreeVar RTyCon RTyVar where
  freeVars = (RTV <$>) . tyConTyVars . rTyCon

-- MOVE TO TYPES
instance FreeVar String String where
  freeVars _ = []

ppClass_String    c _  = pprint c <+> text "..."
ppClass_ClassPred c ts = sDocDoc $ pprClassPred c (toType <$> ts)

-- Eq Instances ------------------------------------------------------

-- MOVE TO TYPES
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
eqRSort m (RFun _ t1 t2 _) (RFun _ t1' t2' _) 
  = eqRSort m t1 t1' && eqRSort m t2 t2'
eqRSort m (RAppTy t1 t2 _) (RAppTy t1' t2' _) 
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
  compare x y = compare (rTyCon x) (rTyCon y)

instance Eq RTyCon where
  x == y = (rTyCon x) == (rTyCon y)

instance Hashable RTyCon where
  hashWithSalt i = hashWithSalt i . rTyCon  

--------------------------------------------------------------------
---------------------- Helper Functions ----------------------------
--------------------------------------------------------------------

rVar        = (`RVar` top) . RTV 
rTyVar      = RTV

normalizePds t = addPds ps t'
  where (t', ps) = nlzP [] t

rPred p t = RAllP p t
rApp c    = RApp (RTyCon c [] (mkTyConInfo c [] [] Nothing)) 


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
nlzP ps t@(RCls _ _)
 = (t, ps)
nlzP ps (RAllP p t)
 = (t', [p] ++ ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@(ROth _)
 = (t, ps)
nlzP ps t@(REx _ _ _) 
 = (t, ps) 
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
  where eqt t1 t2 = {- render -} (toRSort t1) == {- render -} (toRSort t2)
        msg = printf "strengthen on differently shaped reftypes \nt1 = %s [shape = %s]\nt2 = %s [shape = %s]" 
                (showpp t1) (showpp (toRSort t1)) (showpp t2) (showpp (toRSort t2))

unifyShape :: ( RefTypable p c tv r
              , FreeVar c tv
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
  where eqt t1 t2 = showpp (toRSort t1) == showpp (toRSort t2)
         
-- strengthenRefType_ :: RefTypable p c tv r =>RType p c tv r -> RType p c tv r -> RType p c tv r
strengthenRefType_ (RAllT a1 t1) (RAllT _ t2)
  = RAllT a1 $ strengthenRefType_ t1 t2

strengthenRefType_ (RAllP p1 t1) (RAllP _ t2)
  = RAllP p1 $ strengthenRefType_ t1 t2

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
          rs  = {- tracePpr msg $ -} meets rs1 rs2
          msg = "strengthenRefType_: RApp rs1 = " ++ showpp rs1 ++ " rs2 = " ++ showpp rs2


strengthenRefType_ (RVar v1 r1)  (RVar _ r2)
  = RVar v1 ({- tracePpr msg $ -} r1 `meet` r2)
    where msg = "strengthenRefType_: RVAR r1 = " ++ showpp r1 ++ " r2 = " ++ showpp r2
 
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
strengthen (RAppTy t1 t2 r) r'  = RAppTy t1 t2 (r `meet` r')
strengthen t _                  = t 

expandRApp tce tyi (RApp rc ts rs r)
  = RApp rc' ts (appRefts rc' rs) r
    where rc' = appRTyCon tce tyi rc ts

expandRApp _ _ t
  = t

appRTyCon tce tyi rc@(RTyCon c _ _) ts = RTyCon c ps' (rTyConInfo rc'')
  where ps' = map (subts (zip (RTV <$> αs) (toRSort <$> ts))) (rTyConPs rc')
        rc' = M.lookupDefault rc c tyi
        αs  = TC.tyConTyVars $ rTyCon rc'
        rc'' = if isNumeric tce rc' then addNumSizeFun rc' else rc'
isNumeric tce c 
  =  (fromMaybe (stringFTycon $ tyConName (rTyCon c)))
       (M.lookup (rTyCon c) tce) == intFTyCon

addNumSizeFun c 
  = c {rTyConInfo=(rTyConInfo c){sizeFunction = Just EVar}}

appRefts rc [] = RPoly [] . ofRSort . ptype <$> (rTyConPs rc)
appRefts rc rs = safeZipWith ("appRefts" ++ showFix rc) toPoly rs (rTyConPs rc)

toPoly (RPoly ss t) rc 
  | length (pargs rc) == length ss 
  = RPoly ss t
  | otherwise          
  = RPoly ([(s, t) | (t, s, _) <- pargs rc]) t
toPoly (RMono ss r) t 
  = RPoly ss $ (ofRSort $ ptype t) `strengthen` r  

generalize t = mkUnivs (freeTyVars t) [] t 
         
freeTyVars (RAllP _ t)     = freeTyVars t
freeTyVars (RAllT α t)     = freeTyVars t L.\\ [α]
freeTyVars (RFun _ t t' _) = freeTyVars t `L.union` freeTyVars t' 
freeTyVars (RApp _ ts _ _) = L.nub $ concatMap freeTyVars ts
freeTyVars (RCls _ ts)     = []
freeTyVars (RVar α _)      = [α] 
freeTyVars (RAllE _ _ t)   = freeTyVars t
freeTyVars (REx _ _ t)     = freeTyVars t
freeTyVars (RExprArg _)    = []
freeTyVars (RAppTy t t' _) = freeTyVars t `L.union` freeTyVars t'
freeTyVars t               = errorstar ("RefType.freeTyVars cannot handle" ++ show t)

--getTyVars = everything (++) ([] `mkQ` f)
--  where f ((RVar α' _) :: SpecType) = [α'] 
--        f _                         = []

tyClasses (RAllP _ t)     = tyClasses t
tyClasses (RAllT α t)     = tyClasses t
tyClasses (RAllE _ _ t)   = tyClasses t
tyClasses (REx _ _ t)     = tyClasses t
tyClasses (RFun _ t t' _) = tyClasses t ++ tyClasses t'
tyClasses (RAppTy t t' _) = tyClasses t ++ tyClasses t'
tyClasses (RApp _ ts _ _) = concatMap tyClasses ts 
tyClasses (RCls c ts)     = (c, ts) : concatMap tyClasses ts 
tyClasses (RVar α _)      = [] 
tyClasses t               = errorstar ("RefType.tyClasses cannot handle" ++ show t)



--getTyClasses = everything (++) ([] `mkQ` f)
--  where f ((RCls c ts) :: SpecType) = [(c, ts)]
--        f _                        = []



----------------------------------------------------------------
---------------------- Strictness ------------------------------
----------------------------------------------------------------

instance (NFData a, NFData b, NFData t) => NFData (Ref t a b) where
  rnf (RMono s a) = rnf s `seq` rnf a
  rnf (RPoly s b) = rnf s `seq` rnf b

instance (NFData a, NFData b, NFData c, NFData e) => NFData (RType a b c e) where
  rnf (RVar α r)       = rnf α `seq` rnf r 
  rnf (RAllT α t)      = rnf α `seq` rnf t
  rnf (RAllP π t)      = rnf π `seq` rnf t
  rnf (RFun x t t' r)  = rnf x `seq` rnf t `seq` rnf t' `seq` rnf r
  rnf (RApp _ ts rs r) = rnf ts `seq` rnf rs `seq` rnf r
  rnf (RCls c ts)      = c `seq` rnf ts
  rnf (RAllE x t t')   = rnf x `seq` rnf t `seq` rnf t'
  rnf (REx x t t')     = rnf x `seq` rnf t `seq` rnf t'
  rnf (ROth s)         = rnf s
  rnf (RExprArg e)     = rnf e
  rnf (RAppTy t t' r)  = rnf t `seq` rnf t' `seq` rnf r

----------------------------------------------------------------
------------------ Printing Refinement Types -------------------
----------------------------------------------------------------

instance Show RTyVar where
  show = showpp

instance PPrint (UReft r) => Show (UReft r) where
  show = showpp

-- instance (Fixpoint a, Fixpoint b, Fixpoint c) => Fixpoint (a, b, c) where
--   toFix (a, b, c) = hsep ([toFix a ,toFix b, toFix c])

instance (RefTypable p c tv r) => PPrint (RType p c tv r) where
  pprint = ppRType TopPrec

instance PPrint (RType p c tv r) => Show (RType p c tv r) where
  show = showpp

instance Fixpoint RTyCon where
  toFix (RTyCon c _ _) = text $ showPpr c -- <+> text "\n<<" <+> hsep (map toFix ts) <+> text ">>\n"

instance PPrint RTyCon where
  pprint = toFix

instance Show RTyCon where
  show = showpp  


------------------------------------------------------------------------------------------
-- TODO: Rewrite subsTyvars with Traversable
------------------------------------------------------------------------------------------

subsTyVars_meet       = subsTyVars True
subsTyVars_nomeet     = subsTyVars False
subsTyVar_nomeet      = subsTyVar False
subsTyVar_meet        = subsTyVar True
subsTyVars meet ats t = foldl' (flip (subsTyVar meet)) t ats
subsTyVar meet        = subsFree meet S.empty

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
subsFree m s z (RAllE x t t')
  = RAllE x (subsFree m s z t) (subsFree m s z t')
subsFree m s z (REx x t t')
  = REx x (subsFree m s z t) (subsFree m s z t')
subsFree m s z@(_, _, _) (RAppTy t t' r)
  = subsFreeRAppTy m s (subsFree m s z t) (subsFree m s z t') r
subsFree _ _ _ t@(RExprArg _)        
  = t
subsFree _ _ _ t@(ROth _)        
  = t

-- subsFree _ _ _ t      
--   = errorstar $ "subsFree fails on: " ++ showFix t

subsFrees m s zs t = foldl' (flip(subsFree m s)) t zs

-- GHC INVARIANT: RApp is Type Application to something other than TYCon
subsFreeRAppTy m s (RApp c ts rs r) t' r'
  = mkRApp m s c (ts++[t']) rs r r'
subsFreeRAppTy m s t t' r'
  = RAppTy t t' r'

mkRApp m s c ts rs r r'
  | isFun c, [t1, t2] <- ts
  = RFun dummySymbol t1 t2 $ refAppTyToFun r'
  | otherwise 
  = subsFrees m s zs $ RApp c ts rs $ r `meet` (refAppTyToApp r')
  where zs = [(tv, toRSort t, t) | (tv, t) <- zip (freeVars c) ts]

refAppTyToFun r
  | isTauto r = r
  | otherwise = errorstar "RefType.refAppTyToFun"

refAppTyToApp r
  | isTauto r = r
  | otherwise = errorstar "RefType.refAppTyToApp"

-- subsFreeRef ::  (Ord tv, SubsTy tv ty r, SubsTy tv ty (PVar ty), SubsTy tv ty c, Reftable r, Monoid r, Subable r, RefTypable p c tv (PVar ty) r) => Bool -> S.Set tv -> (tv, ty, RType p c tv (PVar ty) r) -> Ref r (RType p c tv (PVar ty) r) -> Ref r (RType p c tv (PVar ty) r)

subsFreeRef m s (α', τ', t')  (RPoly ss t) 
  = RPoly (mapSnd (subt (α', τ')) <$> ss) $ subsFree m s (α', τ', fmap (\_ -> top) t') t
subsFreeRef _ _ (α', τ', _) (RMono ss r) 
  = RMono (mapSnd (subt (α', τ')) <$> ss) $ {- subt (α', τ') -} r

-------------------------------------------------------------------
------------------- Type Substitutions ----------------------------
-------------------------------------------------------------------

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

instance SubsTy RTyVar RSort SpecType where   
  subt (α, τ) = subsTyVar_meet (α, τ, ofRSort τ)

instance SubsTy RTyVar RTyVar SpecType where   
  subt (α, a) = subt (α, RVar a () :: RSort)


instance SubsTy RTyVar RSort RSort where   
  subt (α, τ) = subsTyVar_meet (α, τ, ofRSort τ)

-- Here the "String" is a Bare-TyCon. TODO: wrap in newtype 
instance SubsTy String BSort String where
  subt _ t = t

instance SubsTy String BSort BSort where
  subt (α, τ) = subsTyVar_meet (α, τ, ofRSort τ)

instance (SubsTy tv ty (UReft r), SubsTy tv ty (RType p c tv ())) => SubsTy tv ty (Ref (RType p c tv ()) (UReft r) (RType p c tv (UReft r)))  where
  subt m (RMono ss p) = RMono ((mapSnd (subt m)) <$> ss) $ subt m p
  subt m (RPoly ss t) = RPoly ((mapSnd (subt m)) <$> ss) $ fmap (subt m) t
 
subvUReft     :: (UsedPVar -> UsedPVar) -> UReft Reft -> UReft Reft
subvUReft f (U r p) = U r (subvPredicate f p)

subvPredicate :: (UsedPVar -> UsedPVar) -> Predicate -> Predicate 
subvPredicate f (Pr pvs) = Pr (f <$> pvs)

---------------------------------------------------------------


-- ofType ::  Reftable r => Type -> RRType r
ofType = ofType_ . expandTypeSynonyms 

ofType_ (TyVarTy α)     
  = rVar α
ofType_ (FunTy τ τ')    
  = rFun dummySymbol (ofType_ τ) (ofType_ τ') 
ofType_ (ForAllTy α τ)  
  = RAllT (rTyVar α) $ ofType_ τ  
-- ofType_ τ
--   | isPredTy τ
--   = ofPredTree (classifyPredType τ)  
ofType_ τ
  | Just t <- ofPredTree (classifyPredType τ)
  = t
ofType_ (TyConApp c τs)
  | TC.isSynTyCon c
  = ofType_ $ substTyWith αs τs τ
  | otherwise
  = rApp c (ofType_ <$> τs) [] top 
  where (αs, τ) = TC.synTyConDefn c
ofType_ (AppTy t1 t2)
  = RAppTy (ofType_ t1) (ofType t2) top              
-- ofType_ τ               
--   = errorstar ("ofType cannot handle: " ++ showPpr τ)

ofPredTree (ClassPred c τs)
  = Just $ RCls c (ofType_ <$> τs)
ofPredTree _
  = Nothing

----------------------------------------------------------------
------------------- Converting to Fixpoint ---------------------
----------------------------------------------------------------


varSymbol ::  Var -> Symbol
varSymbol v 
  | us `isSuffixOf` vs = stringSymbol vs  
  | otherwise          = stringSymbol $ vs ++ [symSepName] ++ us
  where us  = showPpr $ getDataConVarUnique v
        vs  = showPpr v

pprShort    =  dropModuleNames . showPpr 

dataConSymbol ::  DataCon -> Symbol
dataConSymbol = varSymbol . dataConWorkId

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
  = top
dataConReft c xs
  = Reft (vv_, [RConc (PAtom Eq (EVar vv_) dcValue)])
  where dcValue | null xs && null (dataConUnivTyVars c) 
                = EVar $ dataConSymbol c
                | otherwise
                = EApp (dataConSymbol c) (EVar <$> xs)

isBaseDataCon c = and $ isBaseTy <$> dataConOrigArgTys c ++ dataConRepArgTys c

isBaseTy (TyVarTy _)     = True
isBaseTy (AppTy t1 t2)   = False
isBaseTy (TyConApp _ ts) = and $ isBaseTy <$> ts
isBaseTy (FunTy _ _)     = False
isBaseTy (ForAllTy _ _)  = False

-- mkProp x = PBexp (EApp (S propConName) [EVar x])

vv_ = vv Nothing

dataConMsReft ty ys  = subst su (rTypeReft t) 
  where (xs, ts, t)  = bkArrow $ thd3 $ bkUniv ty
        su           = mkSubst [(x, EVar y) | ((x,_), y) <- zip (zip xs ts) ys] 

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
toType (RVar (RTV α) _)        
  = TyVarTy α
toType (RApp (RTyCon {rTyCon = c}) ts _ _)   
  = TyConApp c (toType <$> ts)
toType (RCls c ts)   
  = predTreePredType $ ClassPred c (toType <$> ts)
toType (RAllE _ _ t)
  = toType t
toType (REx _ _ t)
  = toType t
toType (RAppTy t t' _)   
  = AppTy (toType t) (toType t')
toType t@(RExprArg _)
  = errorstar $ "RefType.toType cannot handle: " ++ show t
toType t@(ROth _)      
  = errorstar $ "RefType.toType cannot handle: " ++ show t


---------------------------------------------------------------
----------------------- Typing Literals -----------------------
---------------------------------------------------------------

-- makeRTypeBase :: Type -> Reft -> RefType 
makeRTypeBase (TyVarTy α)    x       
  = RVar (rTyVar α) x 
makeRTypeBase (TyConApp c _) x 
  = rApp c [] [] x
makeRTypeBase _              _
  = error "RefType : makeRTypeBase"

literalFRefType tce l 
  = makeRTypeBase (literalType l) (literalFReft tce l) 

literalFReft tce = maybe top exprReft . snd . literalConst tce

 -- exprReft . snd . literalConst tce 

-- | `literalConst` returns `Nothing` for unhandled lits because
--    otherwise string-literals show up as global int-constants 
--    which blow up qualifier instantiation. 

literalConst tce l         = (sort, mkLit l)
  where 
    sort                   = typeSort tce $ literalType l 
    sym                    = stringSymbol $ "$$" ++ showPpr l
    mkLit (MachInt    n)   = mkI n
    mkLit (MachInt64  n)   = mkI n
    mkLit (MachWord   n)   = mkI n
    mkLit (MachWord64 n)   = mkI n
    mkLit (LitInteger n _) = mkI n
    mkLit _                = Nothing -- ELit sym sort
    mkI                    = Just . ECon . I  

---------------------------------------------------------------
---------------- Annotations and Solutions --------------------
---------------------------------------------------------------

rTypeSortedReft       ::  (PPrint r, Reftable r) => TCEmb TyCon -> RRType r -> SortedReft
rTypeSortedReft emb t = RR (rTypeSort emb t) (rTypeReft t)

rTypeSort     ::  (PPrint r, Reftable r) => TCEmb TyCon -> RRType r -> Sort
rTypeSort tce = typeSort tce . toType


------------------------------------------------------------------------
---------------- Auxiliary Stuff Used Elsewhere ------------------------
------------------------------------------------------------------------

-- MOVE TO TYPES
instance (Show tv, Show ty) => Show (RTAlias tv ty) where
  show (RTA n as xs t p) = printf "type %s %s %s = %s -- defined at %s" n 
                           (L.intercalate " " (show <$> as)) 
                           (L.intercalate " " (show <$> xs))
                           (show t) (show p) 

----------------------------------------------------------------
------------ From Old Fixpoint ---------------------------------
----------------------------------------------------------------

typeUniqueSymbol :: Type -> Symbol 
typeUniqueSymbol = stringSymbol . typeUniqueString 


fApp c ts 
  | c == intFTyCon  = FInt
  | otherwise       = FApp c ts

typeSort :: TCEmb TyCon -> Type -> Sort 
typeSort tce τ@(ForAllTy _ _) 
  = typeSortForAll tce τ
typeSort tce (FunTy τ1 τ2) 
  = typeSortFun tce τ1 τ2
typeSort tce (TyConApp c τs)
  = fApp ftc (typeSort tce <$> τs)
  where ftc = fromMaybe (stringFTycon $ tyConName c) (M.lookup c tce) 
typeSort _ τ
  = FObj $ typeUniqueSymbol τ
 
typeSortForAll tce τ 
  = genSort $ typeSort tce tbody
  where genSort (FFunc _ t) = FFunc n (sortSubst su <$> t)
        genSort t           = FFunc n [sortSubst su t]
        (as, tbody)         = splitForAllTys τ 
        su                  = M.fromList $ zip sas (FVar <$>  [0..])
        sas                 = (typeUniqueSymbol . TyVarTy) <$> as
        n                   = length as 

-- sortSubst su t@(FObj x)   = fromMaybe t (M.lookup x su) 
-- sortSubst su (FFunc n ts) = FFunc n (sortSubst su <$> ts)
-- sortSubst su (FApp c ts)  = FApp c  (sortSubst su <$> ts)
-- sortSubst _  t            = t

tyConName c 
  | listTyCon == c    = listConName
  | TC.isTupleTyCon c = tupConName
  | otherwise         = showPpr c

typeSortFun tce τ1 τ2
  = FFunc 0  sos
  where sos  = typeSort tce <$> τs
        τs   = τ1  : grabArgs [] τ2
grabArgs τs (FunTy τ1 τ2 ) = grabArgs (τ1:τs) τ2
grabArgs τs τ              = reverse (τ:τs)

mkDataConIdsTy (dc, t) = [expandProductType id t | id <- dataConImplicitIds dc]

expandProductType x t 
  | ofType (varType x) == toRSort t = (x, t) 
  | otherwise                       = (x, t')
     where t'           = mkArrow as ps xts' tr
           τs           = fst $ splitFunTys $ toType t
           (as, ps, t0) = bkUniv t
           (xs, ts, tr) = bkArrow t0
           xts'         = concatMap mkProductTy $ zip3 τs xs ts
 
mkProductTy (τ, x, t) = maybe [(x, t)] f $ deepSplitProductType_maybe τ
  where f = ((<$>) ((,) dummySymbol . ofType)) . forth4
          
-- Move to misc
forth4 (_, _, _, x)     = x

-----------------------------------------------------------------------------------------
-- | Binders generated by class predicates, typically for constraining tyvars (e.g. FNum)
-----------------------------------------------------------------------------------------

classBinds (RCls c ts) 
  | isNumericClass c = [(rTyVarSymbol a, trueSortedReft FNum) | (RVar a _) <- ts]
classBinds _         = [] 

rTyVarSymbol (RTV α) = typeUniqueSymbol $ TyVarTy α

-----------------------------------------------------------------------------------------
--------------------------- Termination Predicates --------------------------------------
-----------------------------------------------------------------------------------------

isDecreasing (RApp c _ _ _) 
  = isJust (sizeFunction (rTyConInfo c)) 
isDecreasing _ 
  = False

makeDecrType = mkDType [] []

mkDType xvs acc [(v, (x, t@(RApp c _ _ _)))] 
  = (x, ) $ t `strengthen` tr
  where tr     = uTop $ Reft (vv, [RConc $ pOr (r:acc)])
        r      = cmpLexRef xvs (v', vv, f)
        v'     = varSymbol v
        Just f = sizeFunction $ rTyConInfo c
        vv     = stringSymbol "vvRec"

mkDType xvs acc ((v, (x, t@(RApp c _ _ _))):vxts)
  = mkDType ((v', x, f):xvs) (r:acc) vxts
  where r      = cmpLexRef xvs  (v', x, f)
        v'     = varSymbol v
        Just f = sizeFunction $ rTyConInfo c

cmpLexRef vxs (v, x, g)
  = pAnd $ (PAtom Lt (g x) (g v))
         :[PAtom Eq (f y) (f z) | (y, z, f) <- vxs] 
