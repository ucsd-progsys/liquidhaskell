{-# LANGUAGE IncoherentInstances       #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ViewPatterns              #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- TODO(#1918): Only needed for GHC <9.0.1.
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-record-updates #-}

-- | Refinement Types. Mostly mirroring the GHC Type definition, but with
--   room for refinements of various sorts.
-- TODO: Desperately needs re-organization.

module Language.Haskell.Liquid.Types.RefType (

    TyConMap

  -- * Functions for lifting Reft-values to Spec-values
  , uTop, uReft, uRType, uRType', uRTypeGen, uPVar

  -- * Applying a solution to a SpecType
  , applySolution

  -- * Functions for decreasing arguments
  , isDecreasing, makeDecrType, makeNumEnv
  , makeLexRefa

  -- * Functions for manipulating `Predicate`s
  , pdVar
  , findPVar
  , FreeVar, allTyVars, allTyVars', freeTyVars, tyClasses, tyConName

  -- * Quantifying RTypes
  , quantifyRTy
  , quantifyFreeRTy

  -- * RType constructors
  , ofType, toType, bareOfType
  , bTyVar, rTyVar, rVar, rApp, gApp, rEx
  , symbolRTyVar, bareRTyVar
  , tyConBTyCon
  , pdVarReft

  -- * Substitutions
  , subts, subvPredicate, subvUReft
  , subsTyVarMeet, subsTyVarMeet', subsTyVarNoMeet
  , subsTyVarsNoMeet, subsTyVarsMeet

  -- * Destructors
  , addTyConInfo
  , appRTyCon
  , typeUniqueSymbol
  , classBinds
  , isSizeable
  , famInstTyConType
  , famInstArgs

  -- * Manipulating Refinements in RTypes
  , strengthen
  , generalize
  , normalizePds
  , dataConMsReft
  , dataConReft
  , rTypeSortedReft
  , rTypeSort
  , typeSort
  , shiftVV

  -- * TODO: classify these
  -- , mkDataConIdsTy
  , expandProductType
  , mkTyConInfo
  , strengthenRefTypeGen
  , strengthenDataConType
  , isBaseTy
  , updateRTVar, isValKind, kindToRType
  , rTVarInfo

  , tyVarsPosition, Positions(..)

  , isNumeric

  ) where

-- import           GHC.Stack
import Prelude hiding (error)
-- import qualified Prelude
import           Data.Maybe               (fromMaybe, isJust)
import           Data.Monoid              (First(..))
import           Data.Hashable
import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S
import qualified Data.List as L
import           Control.Monad  (void)
import           Text.Printf
import           Text.PrettyPrint.HughesPJ hiding ((<>), first)
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types hiding (DataDecl (..), DataCtor (..), panic, shiftVV, Predicate, isNumeric)
import           Language.Fixpoint.Types.Visitor (mapKVars, Visitable)
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.PrettyPrint

import           Language.Haskell.Liquid.Types.Types hiding (R, DataConP (..))
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types.Names
import qualified Liquid.GHC.Misc as GM
import           Liquid.GHC.Play (mapType, stringClassArg, isRecursivenewTyCon)
import           Liquid.GHC.API        as Ghc hiding ( Expr
                                                                      , Located
                                                                      , tyConName
                                                                      , punctuate
                                                                      , hcat
                                                                      , (<+>)
                                                                      , parens
                                                                      , empty
                                                                      , dcolon
                                                                      , vcat
                                                                      , nest
                                                                      , ($+$)
                                                                      , panic
                                                                      , text
                                                                      )
import           Liquid.GHC.TypeRep () -- Eq Type instance
import Data.List (foldl')







strengthenDataConType :: (Var, SpecType) -> (Var, SpecType)
strengthenDataConType (x, t) = (x, fromRTypeRep trep {ty_res = tres})
  where
    tres     = F.notracepp _msg $ ty_res trep `strengthen` MkUReft (exprReft expr') mempty
    trep     = toRTypeRep t
    _msg     = "STRENGTHEN-DATACONTYPE x = " ++ F.showpp (x, zip xs ts)
    (xs, ts) = dataConArgs trep
    as       = ty_vars  trep
    x'       = symbol x
    expr' | null xs && null as = EVar x'
          | otherwise          = mkEApp (dummyLoc x') (EVar <$> xs)


dataConArgs :: SpecRep -> ([Symbol], [SpecType])
dataConArgs trep = unzip [ (x, t) | (x, t) <- zip xs ts, isValTy t]
  where
    xs           = ty_binds trep
    ts           = ty_args trep
    isValTy      = not . Ghc.isEvVarType . toType False


pdVar :: PVar t -> Predicate
pdVar v        = Pr [uPVar v]

findPVar :: [PVar (RType c tv ())] -> UsedPVar -> PVar (RType c tv ())
findPVar ps upv = PV name ty v (zipWith (\(_, _, e) (t, s, _) -> (t, s, e)) (pargs upv) args)
  where
    PV name ty v args = fromMaybe (msg upv) $ L.find ((== pname upv) . pname) ps
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
uTop r          = MkUReft r mempty

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
        => Semigroup (RType c tv r)  where
  (<>) = strengthenRefType

-- TODO: remove, use only Semigroup?
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

-- MOVE TO TYPES
instance ( SubsTy tv (RType c tv ()) c
         , OkRT c tv r
         , FreeVar c tv
         , SubsTy tv (RType c tv ()) r
         , SubsTy tv (RType c tv ()) (RType c tv ())
         , SubsTy tv (RType c tv ()) tv
         , SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ()))
         )
         => Semigroup (RTProp c tv r) where
  (<>) (RProp s1 (RHole r1)) (RProp s2 (RHole r2))
    | isTauto r1 = RProp s2 (RHole r2)
    | isTauto r2 = RProp s1 (RHole r1)
    | otherwise  = RProp s1 $ RHole $ r1 `meet`
                               subst (mkSubst $ zip (fst <$> s2) (EVar . fst <$> s1)) r2

  (<>) (RProp s1 t1) (RProp s2 t2)
    | isTrivial t1 = RProp s2 t2
    | isTrivial t2 = RProp s1 t1
    | otherwise    = RProp s1 $ t1  `strengthenRefType`
                                subst (mkSubst $ zip (fst <$> s2) (EVar . fst <$> s1)) t2

-- TODO: remove and use only Semigroup?
instance ( SubsTy tv (RType c tv ()) c
         , OkRT c tv r
         , FreeVar c tv
         , SubsTy tv (RType c tv ()) r
         , SubsTy tv (RType c tv ()) (RType c tv ())
         , SubsTy tv (RType c tv ()) tv
         , SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ()))
         )
         => Monoid (RTProp c tv r) where
  mempty  = panic Nothing "mempty: RTProp"
  mappend = (<>)

{-
NV: The following makes ghc diverge thus dublicating the code
instance ( OkRT c tv r
         , FreeVar c tv
         , SubsTy tv (RType c tv ()) r
         , SubsTy tv (RType c tv ()) (RType c tv ())
         , SubsTy tv (RType c tv ()) c
         , SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ()))
         , SubsTy tv (RType c tv ()) tv
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
-}

instance Reftable (RTProp RTyCon RTyVar (UReft Reft)) where
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

instance Reftable (RTProp RTyCon RTyVar ()) where
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

instance Reftable (RTProp BTyCon BTyVar (UReft Reft)) where
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

instance Reftable (RTProp BTyCon BTyVar ())  where
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

instance Reftable (RTProp RTyCon RTyVar Reft) where
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

instance (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r, Reftable (RTProp RTyCon RTyVar r))
    => Reftable (RType RTyCon RTyVar r) where
  isTauto     = isTrivial
  ppTy        = panic Nothing "ppTy RProp Reftable"
  toReft      = panic Nothing "toReft on RType"
  params      = panic Nothing "params on RType"
  bot         = panic Nothing "bot on RType"
  ofReft      = panic Nothing "ofReft on RType"


instance Reftable (RType BTyCon BTyVar (UReft Reft)) where
  isTauto     = isTrivial
  top t       = mapReft top t
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
  toFix = text . GM.showPpr

-- MOVE TO TYPES
class FreeVar a v where
  freeVars :: a -> [v]

-- MOVE TO TYPES
instance FreeVar RTyCon RTyVar where
  freeVars = (RTV <$>) . GM.tyConTyVarsDef . rtc_tc

-- MOVE TO TYPES
instance FreeVar BTyCon BTyVar where
  freeVars _ = []

-- Eq Instances ------------------------------------------------------

-- MOVE TO TYPES
instance (Eq c, Eq tv, Hashable tv, PPrint tv, TyConable c, PPrint c, Reftable (RTProp c tv ()))
      => Eq (RType c tv ()) where
  (==) = eqRSort M.empty

eqRSort :: (Eq a, Eq k, Hashable k, TyConable a, PPrint a, PPrint k, Reftable (RTProp a k ()))
        => M.HashMap k k -> RType a k () -> RType a k () -> Bool
eqRSort m (RAllP _ t) (RAllP _ t')
  = eqRSort m t t'
eqRSort m (RAllP _ t) t'
  = eqRSort m t t'
eqRSort m (RAllT a t _) (RAllT a' t' _)
  | a == a'
  = eqRSort m t t'
  | otherwise
  = eqRSort (M.insert (ty_var_value a') (ty_var_value a) m) t t'
eqRSort m (RAllT _ t _) t'
  = eqRSort m t t'
eqRSort m t (RAllT _ t' _)
  = eqRSort m t t'
eqRSort m (RFun _ _ t1 t2 _) (RFun _ _ t1' t2' _)
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

--------------------------------------------------------------------------------
-- | Wrappers for GHC Type Elements --------------------------------------------
--------------------------------------------------------------------------------

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

-- TyCon isn't comparable
--instance Ord RTyCon where
--  compare x y = compare (rtc_tc x) (rtc_tc y)

instance Hashable RTyCon where
  hashWithSalt i = hashWithSalt i . rtc_tc

--------------------------------------------------------------------------------
-- | Helper Functions (RJ: Helping to do what?) --------------------------------
--------------------------------------------------------------------------------

rVar :: Monoid r => TyVar -> RType c RTyVar r
rVar   = (`RVar` mempty) . RTV

rTyVar :: TyVar -> RTyVar
rTyVar = RTV

updateRTVar :: Monoid r => RTVar RTyVar i -> RTVar RTyVar (RType RTyCon RTyVar r)
updateRTVar (RTVar (RTV a) _) = RTVar (RTV a) (rTVarInfo a)

rTVar :: Monoid r => TyVar -> RTVar RTyVar (RRType r)
rTVar a = RTVar (RTV a) (rTVarInfo a)

bTVar :: Monoid r => TyVar -> RTVar BTyVar (BRType r)
bTVar a = RTVar (BTV (symbol a)) (bTVarInfo a)

bTVarInfo :: Monoid r => TyVar -> RTVInfo (BRType r)
bTVarInfo = mkTVarInfo kindToBRType

rTVarInfo :: Monoid r => TyVar -> RTVInfo (RRType r)
rTVarInfo = mkTVarInfo kindToRType

mkTVarInfo :: (Kind -> s) -> TyVar -> RTVInfo s
mkTVarInfo k2t a = RTVInfo
  { rtv_name   = symbol    $ varName a
  , rtv_kind   = k2t       $ tyVarKind a
  , rtv_is_val = isValKind $ tyVarKind a
  , rtv_is_pol = True
  }

kindToRType :: Monoid r => Type -> RRType r
kindToRType = kindToRType_ ofType

kindToBRType :: Monoid r => Type -> BRType r
kindToBRType = kindToRType_ bareOfType

kindToRType_ :: (Type -> z) -> Type -> z
kindToRType_ ofType'       = ofType' . go
  where
    go t
     | t == typeSymbolKind = stringTy
     | t == naturalTy      = intTy
     | otherwise           = t

isValKind :: Kind -> Bool
isValKind x0 =
    let x = expandTypeSynonyms x0
     in x == naturalTy || x == typeSymbolKind

bTyVar :: Symbol -> BTyVar
bTyVar      = BTV

symbolRTyVar :: Symbol -> RTyVar
symbolRTyVar = rTyVar . GM.symbolTyVar

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
rEx xts rt = foldr (\(x, tx) t -> REx x tx t) rt xts

rApp :: TyCon
     -> [RType RTyCon tv r]
     -> [RTProp RTyCon tv r]
     -> r
     -> RType RTyCon tv r
rApp c = RApp (tyConRTyCon c)

gApp :: TyCon -> [RTyVar] -> [PVar a] -> SpecType
gApp tc αs πs = rApp tc
                  [rVar α | RTV α <- αs]
                  (rPropP [] . pdVarReft <$> πs)
                  mempty

pdVarReft :: PVar t -> UReft Reft
pdVarReft = (\p -> MkUReft mempty p) . pdVar

tyConRTyCon :: TyCon -> RTyCon
tyConRTyCon c = RTyCon c [] (mkTyConInfo c [] [] Nothing)

-- bApp :: (Monoid r) => TyCon -> [BRType r] -> BRType r
bApp :: TyCon -> [BRType r] -> [BRProp r] -> r -> BRType r
bApp c = RApp (tyConBTyCon c)

tyConBTyCon :: TyCon -> BTyCon
tyConBTyCon = mkBTyCon . fmap tyConName . GM.locNamedThing
-- tyConBTyCon = mkBTyCon . fmap symbol . locNamedThing

--- NV TODO : remove this code!!!

addPds :: Foldable t
       => t (PVar (RType c tv ())) -> RType c tv r -> RType c tv r
addPds ps (RAllT v t r) = RAllT v (addPds ps t) r
addPds ps t             = foldl' (flip rPred) t ps

nlzP :: (OkRT c tv r) => [PVar (RType c tv ())] -> RType c tv r -> (RType c tv r, [PVar (RType c tv ())])
nlzP ps t@(RVar _ _ )
 = (t, ps)
nlzP ps (RImpF b i t1 t2 r)
 = (RImpF b i t1' t2' r, ps ++ ps1 ++ ps2)
  where (t1', ps1) = nlzP [] t1
        (t2', ps2) = nlzP [] t2
nlzP ps (RFun b i t1 t2 r)
 = (RFun b i t1' t2' r, ps ++ ps1 ++ ps2)
  where (t1', ps1) = nlzP [] t1
        (t2', ps2) = nlzP [] t2
nlzP ps (RAppTy t1 t2 r)
 = (RAppTy t1' t2' r, ps ++ ps1 ++ ps2)
  where (t1', ps1) = nlzP [] t1
        (t2', ps2) = nlzP [] t2
nlzP ps (RAllT v t r)
 = (RAllT v t' r, ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@RApp{}
 = (t, ps)
nlzP ps (RAllP p t)
 = (t', [p] ++ ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@REx{}
 = (t, ps)
nlzP ps t@(RRTy _ _ _ t')
 = (t, ps ++ ps')
 where ps' = snd $ nlzP [] t'
nlzP ps t@RAllE{}
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

strengthenRefTypeGen = strengthenRefType_ f
  where
    f (RVar v1 r1) t  = RVar v1 (r1 `meet` fromMaybe mempty (stripRTypeBase t))
    f t (RVar _ r1)  = t `strengthen` r1
    f t1 t2           = panic Nothing $ printf "strengthenRefTypeGen on differently shaped types \nt1 = %s [shape = %s]\nt2 = %s [shape = %s]"
                         (pprRaw t1) (showpp (toRSort t1)) (pprRaw t2) (showpp (toRSort t2))

pprRaw :: (OkRT c tv r) => RType c tv r -> String
pprRaw = render . rtypeDoc Full

{- [NOTE:StrengthenRefType] disabling the `meetable` check because

      (1) It requires the 'TCEmb TyCon' to deal with the fact that sometimes,
          GHC uses the "Family Instance" TyCon e.g. 'R:UniquePerson' and sometimes
          the vanilla TyCon App form, e.g. 'Unique Person'
      (2) We could pass in the TCEmb but that would break the 'Monoid' instance for
          RType. The 'Monoid' instance was was probably a bad idea to begin with,
          and we probably ought to do away with it entirely, but thats a battle I'll
          leave for another day.

    Consequently, its up to users of `strengthenRefType` (and associated functions)
    to make sure that the two types are compatible. For an example, see 'meetVarTypes'.
 -}

strengthenRefType t1 t2
  -- | _meetable t1 t2
  = strengthenRefType_ const t1 t2
  -- | otherwise
  -- = panic Nothing msg
  -- where
  --   msg = printf "strengthen on differently shaped reftypes \nt1 = %s [shape = %s]\nt2 = %s [shape = %s]"
  --           (showpp t1) (showpp (toRSort t1)) (showpp t2) (showpp (toRSort t2))

_meetable :: (OkRT c tv r) => RType c tv r -> RType c tv r -> Bool
_meetable t1 t2 = toRSort t1 == toRSort t2

strengthenRefType_ f (RAllT a1 t1 r1) (RAllT a2 t2 r2)
  = RAllT a1 (strengthenRefType_ f t1 (subsTyVarMeet (ty_var_value a2, toRSort t, t) t2)) (r1 `meet` r2)
  where t = RVar (ty_var_value a1) mempty

strengthenRefType_ f (RAllT a t1 r1) t2
  = RAllT a (strengthenRefType_ f t1 t2) r1

strengthenRefType_ f t1 (RAllT a t2 r2)
  = RAllT a (strengthenRefType_ f t1 t2) r2

strengthenRefType_ f (RAllP p1 t1) (RAllP _ t2)
  = RAllP p1 $ strengthenRefType_ f t1 t2

strengthenRefType_ f (RAllP p t1) t2
  = RAllP p $ strengthenRefType_ f t1 t2

strengthenRefType_ f t1 (RAllP p t2)
  = RAllP p $ strengthenRefType_ f t1 t2

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

strengthenRefType_ f (RImpF x1 i t1 t1' r1) (RImpF x2 _ t2 t2' r2)
  = RImpF x2 i t t' (r1 `meet` r2)
    where t  = strengthenRefType_ f t1 t2
          t' = strengthenRefType_ f (subst1 t1' (x1, EVar x2)) t2'

-- YL: Evidence that we need a Monoid instance for RFInfo?
strengthenRefType_ f (RFun x1 i1 t1 t1' r1) (RFun x2 i2 t2 t2' r2)
  | x2 /= F.dummySymbol
  = RFun x2 i1{permitTC = getFirst b} t t' (r1 `meet` r2)
    where t  = strengthenRefType_ f t1 t2
          t' = strengthenRefType_ f (subst1 t1' (x1, EVar x2)) t2'
          b  = First (permitTC i1) <> First (permitTC i2)

strengthenRefType_ f (RFun x1 i1 t1 t1' r1) (RFun x2 i2 t2 t2' r2)
  = RFun x1 i1{permitTC = getFirst b} t t' (r1 `meet` r2)
    where t  = strengthenRefType_ f t1 t2
          t' = strengthenRefType_ f t1' (subst1 t2' (x2, EVar x1))
          b  = First (permitTC i1) <> First (permitTC i2)

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
strengthen (RApp c ts rs r) r'  = RApp c ts rs (r `F.meet` r')
strengthen (RVar a r) r'        = RVar a       (r `F.meet` r')
strengthen (RImpF b i t1 t2 r) r' = RImpF b i t1 t2 (r `F.meet` r')
strengthen (RFun b i t1 t2 r) r'  = RFun b i t1 t2 (r `F.meet` r')
strengthen (RAppTy t1 t2 r) r'  = RAppTy t1 t2 (r `F.meet` r')
strengthen (RAllT a t r)    r'  = RAllT a t    (r `F.meet` r')
strengthen t _                  = t


quantifyRTy :: (Monoid r, Eq tv) => [RTVar tv (RType c tv ())] -> RType c tv r -> RType c tv r
quantifyRTy tvs ty = foldr rAllT ty tvs
  where rAllT a t = RAllT a t mempty

quantifyFreeRTy :: (Monoid r, Eq tv) => RType c tv r -> RType c tv r
quantifyFreeRTy ty = quantifyRTy (freeTyVars ty) ty


-------------------------------------------------------------------------
addTyConInfo :: (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r, Reftable (RTProp RTyCon RTyVar r))
             => TCEmb TyCon
             -> TyConMap
             -> RRType r
             -> RRType r
-------------------------------------------------------------------------
addTyConInfo tce tyi = mapBot (expandRApp tce tyi)

-------------------------------------------------------------------------
expandRApp :: (PPrint r, Reftable r, SubsTy RTyVar RSort r, Reftable (RRProp r))
           => TCEmb TyCon -> TyConMap -> RRType r -> RRType r
-------------------------------------------------------------------------
expandRApp tce tyi t@RApp{} = RApp rc' ts rs' r
  where
    RApp rc ts rs r            = t
    (rc', _)                   = appRTyCon tce tyi rc as
    pvs                        = rTyConPVs rc'
    rs'                        = applyNonNull rs0 (rtPropPV rc pvs) rs
    rs0                        = rtPropTop <$> pvs
    n                          = length fVs
    fVs                        = GM.tyConTyVarsDef $ rtc_tc rc
    as                         = choosen n ts (rVar <$> fVs)
expandRApp _ _ t               = t

choosen :: Int -> [a] -> [a] -> [a]
choosen 0 _ _           = []
choosen i (x:xs) (_:ys) = x:choosen (i-1) xs ys
choosen i []     (y:ys) = y:choosen (i-1) [] ys
choosen _ _ _           = impossible Nothing "choosen: this cannot happen"


rtPropTop
  :: (OkRT c tv r,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv,
      SubsTy tv (RType c tv ()) tv,
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
   => PVar (RType c tv ()) -> Ref (RType c tv ()) (RType c tv r)
rtPropTop pv = case ptype pv of
                 PVProp t -> RProp xts $ ofRSort t
                 PVHProp  -> RProp xts mempty
               where
                 xts      =  pvArgs pv

rtPropPV :: (Fixpoint a, Reftable r)
         => a
         -> [PVar (RType c tv ())]
         -> [Ref (RType c tv ()) (RType c tv r)]
         -> [Ref (RType c tv ()) (RType c tv r)]
rtPropPV _rc = zipWith mkRTProp

mkRTProp :: Reftable r
         => PVar (RType c tv ())
         -> Ref (RType c tv ()) (RType c tv r)
         -> Ref (RType c tv ()) (RType c tv r)
mkRTProp pv (RProp ss (RHole r))
  = RProp ss $ ofRSort (pvType pv) `strengthen` r

mkRTProp pv (RProp ss t)
  | length (pargs pv) == length ss
  = RProp ss t
  | otherwise
  = RProp (pvArgs pv) t

pvArgs :: PVar t -> [(Symbol, t)]
pvArgs pv = [(s, t) | (t, s, _) <- pargs pv]

{- | [NOTE:FamInstPredVars] related to [NOTE:FamInstEmbeds]
     See tests/datacon/pos/T1446.hs 
     The function txRefSort converts

        Int<p>              ===> {v:Int | p v}

     which is fine, but also converts

        Field<q> Blob a     ===> {v:Field Blob a | q v}
        
     which is NOT ok, because q expects a different arg.

     The above happens because, thanks to instance-family stuff,
     LH doesn't realize that q is actually an ARG of Field Blob
     Note that Field itself has no args, but Field Blob does...

     That is, it is not enough to store the refined `TyCon` info,
     solely in the `RTyCon` as with family instances, you need BOTH 
     the `TyCon` and the args to determine the extra info. 
     
     We do so in `TyConMap`, and by crucially extending 

     @RefType.appRTyCon@ whose job is to use the Refined @TyCon@ 
     that is, the @RTyCon@ generated from the @TyConP@ to strengthen
     individual occurrences of the TyCon applied to various arguments.

 -}

appRTyCon :: (ToTypeable r) => TCEmb TyCon -> TyConMap -> RTyCon -> [RRType r] -> (RTyCon, [RPVar])
appRTyCon tce tyi rc ts = F.notracepp _msg (resTc, ps'')
  where
    _msg  = "appRTyCon-family: " ++ showpp (Ghc.isFamilyTyCon c, Ghc.tyConRealArity c, toType False <$> ts)
    resTc = RTyCon c ps'' (rtc_info rc'')
    c     = rtc_tc rc

    (rc', ps') = rTyConWithPVars tyi rc (rTypeSort tce <$> ts)
    -- TODO:faminst-preds rc'   = M.lookupDefault rc c (tcmTyRTy tyi)
    -- TODO:faminst-preds ps'   = rTyConPVs rc' 

    -- TODO:faminst-preds: these substitutions may be WRONG if we are using FAMINST.
    ps''  = subts (zip (RTV <$> αs) ts') <$> ps'
      where
        ts' = if null ts then rVar <$> βs else toRSort <$> ts
        αs  = GM.tyConTyVarsDef (rtc_tc rc')
        βs  = GM.tyConTyVarsDef c

    rc''  = if isNumeric tce rc' then addNumSizeFun rc' else rc'

rTyConWithPVars :: TyConMap -> RTyCon -> [F.Sort] -> (RTyCon, [RPVar])
rTyConWithPVars tyi rc ts = case famInstTyConMb tyi rc ts of
  Just fiRc    -> (rc', rTyConPVs fiRc)       -- use the PVars from the family-instance TyCon
  Nothing      -> (rc', ps')                  -- use the PVars from the origin          TyCon
  where
    (rc', ps') = plainRTyConPVars tyi rc

-- | @famInstTyConMb rc args@ uses the @RTyCon@ AND @args@ to see if 
--   this is a family instance @RTyCon@, and if so, returns it.
--   see [NOTE:FamInstPredVars]
--   eg: 'famInstTyConMb tyi Field [Blob, a]' should give 'Just R:FieldBlob' 

famInstTyConMb :: TyConMap -> RTyCon -> [F.Sort] -> Maybe RTyCon
famInstTyConMb tyi rc ts = do
  let c = rtc_tc rc
  n    <- M.lookup c      (tcmFtcArity tyi)
  M.lookup (c, take n ts) (tcmFIRTy    tyi)

famInstTyConType :: Ghc.TyCon -> Maybe Ghc.Type
famInstTyConType c = uncurry Ghc.mkTyConApp <$> famInstArgs c

-- | @famInstArgs c@ destructs a family-instance @TyCon@ into its components, e.g. 
--   e.g. 'famInstArgs R:FieldBlob' is @(Field, [Blob])@ 

famInstArgs :: Ghc.TyCon -> Maybe (Ghc.TyCon, [Ghc.Type])
famInstArgs c = case Ghc.tyConFamInst_maybe c of
    Just (c', ts) -> F.notracepp ("famInstArgs: " ++ F.showpp (c, cArity, ts))
                     $ Just (c', take (length ts - cArity) ts)
    Nothing       -> Nothing
    where
      cArity      = Ghc.tyConRealArity c

-- TODO:faminst-preds: case Ghc.tyConFamInst_maybe c of
-- TODO:faminst-preds:   Just (c', ts) -> F.tracepp ("famInstTyConType: " ++ F.showpp (c, Ghc.tyConArity c, ts)) 
-- TODO:faminst-preds:                    $ Just (famInstType (Ghc.tyConArity c) c' ts)
-- TODO:faminst-preds:   Nothing       -> Nothing

-- TODO:faminst-preds: famInstType :: Int -> Ghc.TyCon -> [Ghc.Type] -> Ghc.Type
-- TODO:faminst-preds: famInstType n c ts = Ghc.mkTyConApp c (take (length ts - n) ts)




-- | @plainTyConPVars@ uses the @TyCon@ to return the 
--   "refined" @RTyCon@ and @RPVars@ from the refined 
--   'data' definition for the @TyCon@, e.g. will use 
--   'List Int' to return 'List<p> Int' (if List has an abs-ref).
plainRTyConPVars :: TyConMap -> RTyCon -> (RTyCon, [RPVar])
plainRTyConPVars tyi rc = (rc', rTyConPVs rc')
  where
    rc'                   = M.lookupDefault rc (rtc_tc rc) (tcmTyRTy tyi)



-- RJ: The code of `isNumeric` is incomprehensible.
-- Please fix it to use intSort instead of intFTyCon
isNumeric :: TCEmb TyCon -> RTyCon -> Bool
isNumeric tce c = F.isNumeric mySort
  where
    -- mySort      = M.lookupDefault def rc tce
    mySort      = maybe def fst (F.tceLookup rc tce)
    def         = FTC . symbolFTycon . dummyLoc . tyConName $ rc
    rc          = rtc_tc c

addNumSizeFun :: RTyCon -> RTyCon
addNumSizeFun c
  = c {rtc_info = (rtc_info c) {sizeFunction = Just IdSizeFun } }


generalize :: (Eq tv, Monoid r) => RType c tv r -> RType c tv r
generalize t = mkUnivs (zip (freeTyVars t) (repeat mempty)) [] t

allTyVars :: (Ord tv) => RType c tv r -> [tv]
allTyVars = sortNub . allTyVars'

allTyVars' :: (Eq tv) => RType c tv r -> [tv]
allTyVars' t = fmap ty_var_value $ vs ++ vs'
  where
    vs      = map fst . fst3 . bkUniv $ t
    vs'     = freeTyVars t


freeTyVars :: Eq tv => RType c tv r -> [RTVar tv (RType c tv ())]
freeTyVars (RAllP _ t)     = freeTyVars t
freeTyVars (RAllT α t _)   = freeTyVars t L.\\ [α]
freeTyVars (RImpF _ _ t t' _)= freeTyVars t `L.union` freeTyVars t'
freeTyVars (RFun _ _ t t' _) = freeTyVars t `L.union` freeTyVars t'
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
tyClasses (RAllT _ t _)   = tyClasses t
tyClasses (RAllE _ _ t)   = tyClasses t
tyClasses (REx _ _ t)     = tyClasses t
tyClasses (RImpF _ _ t t' _) = tyClasses t ++ tyClasses t'
tyClasses (RFun _ _ t t' _) = tyClasses t ++ tyClasses t'
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

subsTyVarsMeet
  :: (Eq tv, Foldable t, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv,
      SubsTy tv (RType c tv ()) tv,
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => t (tv, RType c tv (), RType c tv r) -> RType c tv r -> RType c tv r
subsTyVarsMeet        = subsTyVars True

subsTyVarsNoMeet
  :: (Eq tv, Foldable t, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv,
      SubsTy tv (RType c tv ()) tv,
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => t (tv, RType c tv (), RType c tv r) -> RType c tv r -> RType c tv r
subsTyVarsNoMeet      = subsTyVars False

subsTyVarNoMeet
  :: (Eq tv, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv,
      SubsTy tv (RType c tv ()) tv,
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => (tv, RType c tv (), RType c tv r) -> RType c tv r -> RType c tv r
subsTyVarNoMeet       = subsTyVar False

subsTyVarMeet
  :: (Eq tv, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv,
      SubsTy tv (RType c tv ()) tv,
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => (tv, RType c tv (), RType c tv r) -> RType c tv r -> RType c tv r
subsTyVarMeet         = subsTyVar True

subsTyVarMeet'
  :: (Eq tv, Hashable tv, Reftable r, TyConable c,
      SubsTy tv (RType c tv ()) c, SubsTy tv (RType c tv ()) r,
      SubsTy tv (RType c tv ()) (RType c tv ()), FreeVar c tv,
      SubsTy tv (RType c tv ()) tv,
      SubsTy tv (RType c tv ()) (RTVar tv (RType c tv ())))
  => (tv, RType c tv r) -> RType c tv r -> RType c tv r
subsTyVarMeet' (α, t) = subsTyVarMeet (α, toRSort t, t)

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
subsTyVars meet' ats t = foldl' (flip (subsTyVar meet')) t ats

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
subsTyVar meet'        = subsFree meet' S.empty

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
subsFree m s z@(α, τ,_) (RAllP π t)
  = RAllP (subt (α, τ) π) (subsFree m s z t)
subsFree m s z@(a, τ, _) (RAllT α t r)
  -- subt inside the type variable instantiates the kind of the variable
  = RAllT (subt (a, τ) α) (subsFree m (ty_var_value α `S.insert` s) z t) (subt (a, τ) r)
subsFree m s z@(α, τ, _) (RImpF x i t t' r)
  = RImpF x i (subsFree m s z t) (subsFree m s z t') (subt (α, τ) r)
subsFree m s z@(α, τ, _) (RFun x i t t' r)
  = RFun x i (subsFree m s z t) (subsFree m s z t') (subt (α, τ) r)
subsFree m s z@(α, τ, _) (RApp c ts rs r)
  = RApp c' (subsFree m s z <$> ts) (subsFreeRef m s z <$> rs) (subt (α, τ) r)
    where z' = (α, τ) -- UNIFY: why instantiating INSIDE parameters?
          c' = if α `S.member` s then c else subt z' c
subsFree meet' s (α', τ, t') (RVar α r)
  | α == α' && not (α `S.member` s)
  = if meet' then t' `strengthen` subt (α, τ) r else t'
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


-- | @mkRApp@ is the refined variant of GHC's @mkTyConApp@ which ensures that 
--    that applications of the "function" type constructor are normalized to 
--    the special case @FunTy _@ representation. The extra `_rep1`, and `_rep2` 
--    parameters come from the "levity polymorphism" changes in GHC 8.6 (?)
--    See [NOTE:Levity-Polymorphism]

mkRApp :: (Eq tv, Hashable tv, Reftable r, TyConable c,
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
  | isFun c, [_rep1, _rep2, t1, t2] <- ts
  = RFun dummySymbol defRFInfo t1 t2 (refAppTyToFun r')
  | otherwise
  = subsFrees m s zs (RApp c ts rs (r `meet` r'))
  where
    zs = [(tv, toRSort t, t) | (tv, t) <- zip (freeVars c) ts]

{-| [NOTE:Levity-Polymorphism] 
 
     Thanks to Joachim Brietner and Simon Peyton-Jones!
     With GHC's "levity polymorphism feature", see more here 

         https://stackoverflow.com/questions/35318562/what-is-levity-polymorphism     

     The function type constructor actually has type

        (->) :: forall (r1::RuntimeRep) (r2::RuntimeRep).  TYPE r1 -> TYPE r2 -> TYPE LiftedRep

     so we have to be careful to follow GHC's @mkTyConApp@ 
     
        https://hackage.haskell.org/package/ghc-8.6.4/docs/src/Type.html#mkTyConApp

     which normalizes applications of the `FunTyCon` constructor to use the special 
     case `FunTy _` representation thus, so that we are not stuck with incompatible 
     representations e.g. 

        thing -> thing                                                  ... (using RFun)

     and 

        (-> 'GHC.Types.LiftedRep 'GHC.Types.LiftedRep thing thing)      ... (using RApp)


     More details from Joachim Brietner:

     Now you might think that the function arrow has the following kind: `(->) :: * -> * -> *`.
     But that is not the full truth: You can have functions that accept or return things with 
     different representations than just the usual lifted one.

     So the function arrow actually has kind `(->) :: forall r1 r2. TYPE r1 -> TYPE r2 -> *`.
     And in `(-> 'GHC.Types.LiftedRep 'GHC.Types.LiftedRep thing thing)`  you see this spelled 
     out explicitly. But it really is just `(thing -> thing)`, just printed with more low-level detail.

     Also see

       • https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#levity-polymorphism
       • and other links from https://stackoverflow.com/a/35320729/946226 (edited) 
 -}

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


--------------------------------------------------------------------------------
-- | Type Substitutions --------------------------------------------------------
--------------------------------------------------------------------------------

subts :: (SubsTy tv ty c) => [(tv, ty)] -> c -> c
subts = flip (foldr subt)

instance SubsTy RTyVar (RType RTyCon RTyVar ()) RTyVar where
  subt (RTV x, t) (RTV z) | isTyVar z, tyVarKind z == TyVarTy x
    = RTV (setVarType z $ toType False t)
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

instance SubsTy Symbol Symbol (BRType r) where
  subt (x,y) (RVar v r)
    | BTV x == v = RVar (BTV y) r
    | otherwise  = RVar v r
  subt (x, y) (RAllT (RTVar v i) t r)
    | BTV x == v = RAllT (RTVar v i) t r
    | otherwise  = RAllT (RTVar v i) (subt (x,y) t) r
  subt su (RFun x i t1 t2 r)  = RFun x i (subt su t1) (subt su t2) r
  subt su (RImpF x i t1 t2 r) = RImpF x i (subt su t1) (subt su t2) r
  subt su (RAllP p t)       = RAllP p (subt su t)
  subt su (RApp c ts ps r)  = RApp c (subt su <$> ts) (subt su <$> ps) r
  subt su (RAllE x t1 t2)   = RAllE x (subt su t1) (subt su t2)
  subt su (REx x t1 t2)     = REx x (subt su t1) (subt su t2)
  subt _  (RExprArg e)      = RExprArg e
  subt su (RAppTy t1 t2 r)  = RAppTy (subt su t1) (subt su t2) r
  subt su (RRTy e r o t)    = RRTy [(x, subt su p) | (x,p) <- e] r o (subt su t)
  subt _ (RHole r)          = RHole r

instance SubsTy Symbol Symbol (RTProp BTyCon BTyVar r) where
  subt su (RProp e t) =  RProp [(x, subt su xt) | (x,xt) <- e] (subt su t)



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
    | symbol v == s = FObj $ symbol {- rTyVarSymbol -} α
    | otherwise     = FObj s
  subt _ s          = s


instance SubsTy RTyVar RSort Sort where
  subt (v, sv) (FObj s)
    | symbol v == s = typeSort mempty (toType True sv)
    | otherwise     = FObj s
  subt _ s          = s

instance (SubsTy tv ty ty) => SubsTy tv ty (PVKind ty) where
  subt su (PVProp t) = PVProp (subt su t)
  subt _   PVHProp   = PVHProp

instance (SubsTy tv ty ty) => SubsTy tv ty (PVar ty) where
  subt su (PV n pvk v xts) = PV n (subt su pvk) v [(subt su t, x, y) | (t,x,y) <- xts]

instance SubsTy RTyVar RSort RTyCon where
   subt z c = RTyCon tc ps' i
     where
       tc   = rtc_tc c
       ps'  = subt z <$> rTyConPVs c
       i    = rtc_info c

-- NOTE: This DOES NOT substitute at the binders
instance SubsTy RTyVar RSort PrType where
  subt (α, τ) = subsTyVarMeet (α, τ, ofRSort τ)

instance SubsTy RTyVar RSort SpecType where
  subt (α, τ) = subsTyVarMeet (α, τ, ofRSort τ)

instance SubsTy TyVar Type SpecType where
  subt (α, τ) = subsTyVarMeet (RTV α, ofType τ, ofType τ)

instance SubsTy RTyVar RTyVar SpecType where
  subt (α, a) = subt (α, RVar a () :: RSort)


instance SubsTy RTyVar RSort RSort where
  subt (α, τ) = subsTyVarMeet (α, τ, ofRSort τ)

instance SubsTy tv RSort Predicate where
  subt _ = id -- NV TODO

instance (SubsTy tv ty r) => SubsTy tv ty (UReft r) where
  subt su r = r {ur_reft = subt su $ ur_reft r}

-- Here the "String" is a Bare-TyCon. TODO: wrap in newtype
instance SubsTy BTyVar BSort BTyCon where
  subt _ t = t

instance SubsTy BTyVar BSort BSort where
  subt (α, τ) = subsTyVarMeet (α, τ, ofRSort τ)

instance (SubsTy tv ty (UReft r), SubsTy tv ty (RType c tv ())) => SubsTy tv ty (RTProp c tv (UReft r))  where
  subt m (RProp ss (RHole p)) = RProp (mapSnd (subt m) <$> ss) $ RHole $ subt m p
  subt m (RProp ss t) = RProp (mapSnd (subt m) <$> ss) $ fmap (subt m) t

subvUReft     :: (UsedPVar -> UsedPVar) -> UReft Reft -> UReft Reft
subvUReft f (MkUReft r p) = MkUReft r (subvPredicate f p)

subvPredicate :: (UsedPVar -> UsedPVar) -> Predicate -> Predicate
subvPredicate f (Pr pvs) = Pr (f <$> pvs)

--------------------------------------------------------------------------------
ofType :: Monoid r => Type -> RRType r
--------------------------------------------------------------------------------
ofType      = ofType_ $ TyConv
  { tcFVar  = rVar
  , tcFTVar = rTVar
  , tcFApp  = \c ts -> rApp c ts [] mempty
  , tcFLit  = ofLitType rApp
  }

--------------------------------------------------------------------------------
bareOfType :: Monoid r => Type -> BRType r
--------------------------------------------------------------------------------
bareOfType  = ofType_ $ TyConv
  { tcFVar  = (`RVar` mempty) . BTV . symbol
  , tcFTVar = bTVar
  , tcFApp  = \c ts -> bApp c ts [] mempty
  , tcFLit  = ofLitType bApp
  }

--------------------------------------------------------------------------------
ofType_ :: Monoid r => TyConv c tv r -> Type -> RType c tv r
--------------------------------------------------------------------------------
ofType_ tx = go . expandTypeSynonyms
  where
    go (TyVarTy α)
      = tcFVar tx α
    go (FunTy _ _ τ τ')
      = rFun dummySymbol (go τ) (go τ')
    go (ForAllTy (Bndr α _) τ)
      = RAllT (tcFTVar tx α) (go τ) mempty
    go (TyConApp c τs)
      | Just (αs, τ) <- Ghc.synTyConDefn_maybe c
      = go (substTyWith αs τs τ)
      | otherwise
      = tcFApp tx c (go <$> τs) -- [] mempty
    go (AppTy t1 t2)
      = RAppTy (go t1) (ofType_ tx t2) mempty
    go (LitTy x)
      = tcFLit tx x
    go (CastTy t _)
      = go t
    go (CoercionTy _)
      = errorstar "Coercion is currently not supported"

ofLitType :: (Monoid r) => (TyCon -> [RType c tv r] -> [p] -> r -> RType c tv r) -> TyLit -> RType c tv r
ofLitType rF (NumTyLit _)  = rF intTyCon [] [] mempty
ofLitType rF t@(StrTyLit _)
  | t == holeLit           = RHole mempty
  | otherwise              = rF listTyCon [rF charTyCon [] [] mempty] [] mempty

holeLit :: TyLit
holeLit = StrTyLit "$LH_RHOLE"

data TyConv c tv r = TyConv
  { tcFVar  :: TyVar -> RType c tv r
  , tcFTVar :: TyVar -> RTVar tv (RType c tv ())
  , tcFApp  :: TyCon -> [RType c tv r] -> RType c tv r
  , tcFLit  :: TyLit -> RType c tv r
  }

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
isBaseDataCon c = and $ isBaseTy <$> map irrelevantMult (dataConOrigArgTys c ++ dataConRepArgTys c)

isBaseTy :: Type -> Bool
isBaseTy (TyVarTy _)      = True
isBaseTy (AppTy _ _)      = False
isBaseTy (TyConApp _ ts)  = and $ isBaseTy <$> ts
isBaseTy FunTy{}          = False
isBaseTy (ForAllTy _ _)   = False
isBaseTy (LitTy _)        = True
isBaseTy (CastTy _ _)     = False
isBaseTy (CoercionTy _)   = False


dataConMsReft :: Reftable r => RType c tv r -> [Symbol] -> Reft
dataConMsReft ty ys  = subst su (rTypeReft (ignoreOblig $ ty_res trep))
  where
    trep = toRTypeRep ty
    xs   = ty_binds trep
    ts   = ty_args  trep
    su   = mkSubst $ [(x, EVar y) | ((x, _), y) <- zip (zip xs ts) ys]

--------------------------------------------------------------------------------
-- | Embedding RefTypes --------------------------------------------------------
--------------------------------------------------------------------------------

type ToTypeable r = (Reftable r, PPrint r, SubsTy RTyVar (RRType ()) r, Reftable (RTProp RTyCon RTyVar r))

-- TODO: remove toType, generalize typeSort
-- YL: really should take a type-level Bool
toType  :: (ToTypeable r) => Bool -> RRType r -> Type
toType useRFInfo (RImpF x i t t' r)
 = toType useRFInfo (RFun x i t t' r)
toType useRFInfo (RFun _ RFInfo{permitTC = permitTC} t@(RApp c _ _ _) t' _)
  | useRFInfo && isErasable c  = toType useRFInfo t'
  | otherwise
  = FunTy VisArg Many (toType useRFInfo t) (toType useRFInfo t')
  where isErasable = if permitTC == Just True then isEmbeddedDict else isClass
toType useRFInfo (RFun _ _ t t' _)
  = FunTy VisArg Many (toType useRFInfo t) (toType useRFInfo t')
toType useRFInfo (RAllT a t _) | RTV α <- ty_var_value a
  = ForAllTy (Bndr α Required) (toType useRFInfo t)
toType useRFInfo (RAllP _ t)
  = toType useRFInfo t
toType _ (RVar (RTV α) _)
  = TyVarTy α
toType useRFInfo (RApp RTyCon{rtc_tc = c} ts _ _)
  = TyConApp c (toType useRFInfo <$> filter notExprArg ts)
  where
    notExprArg (RExprArg _) = False
    notExprArg _            = True
toType useRFInfo (RAllE _ _ t)
  = toType useRFInfo t
toType useRFInfo (REx _ _ t)
  = toType useRFInfo t
toType useRFInfo (RAppTy t (RExprArg _) _)
  = toType useRFInfo t
toType useRFInfo (RAppTy t t' _)
  = AppTy (toType useRFInfo t) (toType useRFInfo t')
toType _ t@(RExprArg _)
  = impossible Nothing $ "CANNOT HAPPEN: RefType.toType called with: " ++ show t
toType useRFInfo (RRTy _ _ _ t)
  = toType useRFInfo t
toType _ (RHole _)
  = LitTy holeLit
-- toType t
--  = {- impossible Nothing -} Prelude.error $ "RefType.toType cannot handle: " ++ show t

{- | [NOTE:Hole-Lit] 

We use `toType` to convert RType to GHC.Type to expand any GHC 
related type-aliases, e.g. in Bare.Resolve.expandRTypeSynonyms. 
If the RType has a RHole then what to do?

We, encode `RHole` as `LitTy "LH_HOLE"` -- which is a bit of 
a *hack*. The only saving grace is it is used *temporarily* 
and then swiftly turned back into an `RHole` via `ofType` 
(after GHC has done its business of expansion).

Of course, we hope this doesn't break any GHC invariants!
See issue #1476 and #1477 

The other option is to *not* use `toType` on things that have
holes in them, but this seems worse, e.g. because you may define 
a plain GHC alias like:

    type ToNat a = a -> Nat 

and then you might write refinement types like:

    {-@ foo :: ToNat {v:_ | 0 <= v} @-}

and we'd want to expand the above to

    {-@ foo :: {v:_ | 0 <= v} -> Nat @-}

and then resolve the hole using the (GHC) type of `foo`.

-}

--------------------------------------------------------------------------------
-- | Annotations and Solutions -------------------------------------------------
--------------------------------------------------------------------------------

rTypeSortedReft ::  (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r, Reftable (RTProp RTyCon RTyVar r))
                => TCEmb TyCon -> RRType r -> SortedReft
rTypeSortedReft emb t = RR (rTypeSort emb t) (rTypeReft t)

rTypeSort     ::  (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r, Reftable (RTProp RTyCon RTyVar r))
              => TCEmb TyCon -> RRType r -> Sort
rTypeSort tce = typeSort tce . toType True

--------------------------------------------------------------------------------
applySolution :: (Functor f) => FixSolution -> f SpecType -> f SpecType
--------------------------------------------------------------------------------
applySolution = fmap . fmap . mapReft' . appSolRefa
  where
    mapReft' f (MkUReft (Reft (x, z)) p) = MkUReft (Reft (x, f z)) p

appSolRefa :: Visitable t
           => M.HashMap KVar Expr -> t -> t
appSolRefa s p = mapKVars f p
  where
    f k        = Just $ M.lookupDefault PTop k s

--------------------------------------------------------------------------------
-- shiftVV :: Int -- SpecType -> Symbol -> SpecType
shiftVV :: (TyConable c, F.Reftable (f Reft), Functor f)
        => RType c tv (f Reft) -> Symbol -> RType c tv (f Reft)
--------------------------------------------------------------------------------
shiftVV t@(RApp _ ts rs r) vv'
  = t { rt_args  = subst1 ts (rTypeValueVar t, EVar vv') }
      { rt_pargs = subst1 rs (rTypeValueVar t, EVar vv') }
      { rt_reft  = (`F.shiftVV` vv') <$> r }

shiftVV t@(RImpF _ _ _ _ r) vv'
  = t { rt_reft = (`F.shiftVV` vv') <$> r }

shiftVV t@(RFun _ _ _ _ r) vv'
  = t { rt_reft = (`F.shiftVV` vv') <$> r }

shiftVV t@(RAppTy _ _ r) vv'
  = t { rt_reft = (`F.shiftVV` vv') <$> r }

shiftVV t@(RVar _ r) vv'
  = t { rt_reft = (`F.shiftVV` vv') <$> r }

shiftVV t _
  = t -- errorstar $ "shiftVV: cannot handle " ++ showpp t


--------------------------------------------------------------------------------
-- |Auxiliary Stuff Used Elsewhere ---------------------------------------------
--------------------------------------------------------------------------------

-- MOVE TO TYPES
instance (Show tv, Show ty) => Show (RTAlias tv ty) where
  show (RTA n as xs t) =
    printf "type %s %s %s = %s" (symbolString n)
      (unwords (show <$> as))
      (unwords (show <$> xs))
      (show t)

--------------------------------------------------------------------------------
-- | From Old Fixpoint ---------------------------------------------------------
--------------------------------------------------------------------------------
typeSort :: TCEmb TyCon -> Type -> Sort
typeSort tce = go
  where
    go :: Type -> Sort
    go t@FunTy{}        = typeSortFun tce t
    go τ@(ForAllTy _ _) = typeSortForAll tce τ
    -- go (TyConApp c τs)  = fApp (tyConFTyCon tce c) (go <$> τs)
    go (TyConApp c τs)
      | isNewTyCon c
      , not (isRecursivenewTyCon c)
      = go (Ghc.newTyConInstRhs c τs)
      | otherwise
      = tyConFTyCon tce c (go <$> τs)
    go (AppTy t1 t2)    = fApp (go t1) [go t2]
    go (TyVarTy tv)     = tyVarSort tv
    go (CastTy t _)     = go t
    go τ                = FObj (typeUniqueSymbol τ)

tyConFTyCon :: TCEmb TyCon -> TyCon -> [Sort] -> Sort
tyConFTyCon tce c ts = case tceLookup c tce of
                         Just (t, WithArgs) -> t
                         Just (t, NoArgs)   -> fApp t ts
                         Nothing            -> fApp (fTyconSort niTc) ts
  where
    niTc             = symbolNumInfoFTyCon (dummyLoc $ tyConName c) (isNumCls c) (isFracCls c)
    -- oldRes           = F.notracepp _msg $ M.lookupDefault def c tce
    -- _msg             = "tyConFTyCon c = " ++ show c ++ "default " ++ show (def, Ghc.isFamInstTyCon c)

tyVarSort :: TyVar -> Sort
tyVarSort = FObj . symbol

typeUniqueSymbol :: Type -> Symbol
typeUniqueSymbol = symbol . GM.typeUniqueString

typeSortForAll :: TCEmb TyCon -> Type -> Sort
typeSortForAll tce τ  = F.notracepp ("typeSortForall " ++ showpp τ) $ genSort sbody
  where
    sbody             = typeSort tce tbody
    genSort t         = foldl' (flip FAbs) (sortSubst su t) [i..n+i-1]
    (as, tbody)       = F.notracepp ("splitForallTys" ++ GM.showPpr τ) (splitForAllTyCoVars τ)
    su                = M.fromList $ zip sas (FVar <$>  [i..])
    sas               = symbol <$> as
    n                 = length as
    i                 = sortAbs sbody + 1

-- RJ: why not make this the Symbolic instance?
tyConName :: TyCon -> Symbol
tyConName c
  | listTyCon == c    = listConName
  | Ghc.isTupleTyCon c = tupConName
  | otherwise         = symbol c

typeSortFun :: TCEmb TyCon -> Type -> Sort
typeSortFun tce t = mkFFunc 0 sos
  where
    sos           = typeSort tce <$> τs
    τs            = grabArgs [] t

grabArgs :: [Type] -> Type -> [Type]
grabArgs τs (FunTy _ _ τ1 τ2)
  | Just a <- stringClassArg τ1
  = grabArgs τs (mapType (\t -> if t == a then stringTy else t) τ2)
  -- not ( F.notracepp ("isNonArg: " ++ GM.showPpr τ1) $ isNonValueTy τ1)
  | otherwise
  = grabArgs (τ1:τs) τ2
  -- otherwise
  -- = grabArgs τs τ2
  -- -- | otherwise
  -- -- = grabArgs τs τ2
grabArgs τs τ
  = reverse (τ:τs)


expandProductType :: (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r, Reftable (RTProp RTyCon RTyVar r))
                  => Var -> RType RTyCon RTyVar r -> RType RTyCon RTyVar r
expandProductType x t
  | isTrivial'      = t
  | otherwise       = fromRTypeRep $ trep {ty_binds = xs', ty_info=is', ty_args = ts', ty_refts = rs'}
     where
      isTrivial'    = ofType (varType x) == toRSort t
      τs            = map irrelevantMult $ fst $ splitFunTys $ snd $ splitForAllTyCoVars $ toType False t
      trep          = toRTypeRep t
      (xs',is',ts',rs') = unzip4 $ concatMap mkProductTy $ zip5 τs (ty_binds trep) (ty_info trep) (ty_args trep) (ty_refts trep)

-- splitFunTys :: Type -> ([Type], Type)

data DataConAppContext
  = DataConAppContext
  { dcac_dc      :: !DataCon
  , dcac_tys     :: ![Type]
  , dcac_arg_tys :: ![(Type, StrictnessMark)]
  , dcac_co      :: !Coercion
  }

mkProductTy :: forall t r. (Monoid t, Monoid r)
            => (Type, Symbol, RFInfo, RType RTyCon RTyVar r, t)
            -> [(Symbol, RFInfo, RType RTyCon RTyVar r, t)]
mkProductTy (τ, x, i, t, r) = maybe [(x, i, t, r)] f (deepSplitProductType menv τ)
  where
    f    :: DataConAppContext -> [(Symbol, RFInfo, RType RTyCon RTyVar r, t)]
    f    DataConAppContext{..} = map ((dummySymbol, defRFInfo, , mempty) . ofType . fst) dcac_arg_tys
    menv = (emptyFamInstEnv, emptyFamInstEnv)

-- Copied from GHC 9.0.2.
orElse :: Maybe a -> a -> a
orElse = flip fromMaybe

-- Copied from GHC 9.0.2.
deepSplitProductType :: FamInstEnvs -> Type -> Maybe DataConAppContext
-- If    deepSplitProductType_maybe ty = Just (dc, tys, arg_tys, co)
-- then  dc @ tys (args::arg_tys) :: rep_ty
--       co :: ty ~ rep_ty
-- Why do we return the strictness of the data-con arguments?
-- Answer: see Note [Record evaluated-ness in worker/wrapper]
deepSplitProductType fam_envs ty
  | let (co, ty1) = topNormaliseType_maybe fam_envs ty
                    `orElse` (mkRepReflCo ty, ty)
  , Just (tc, tc_args) <- splitTyConApp_maybe ty1
  , Just con <- tyConSingleDataCon_maybe tc
  , let arg_tys = dataConInstArgTys con tc_args
        strict_marks = dataConRepStrictness con
  = Just DataConAppContext { dcac_dc = con
                           , dcac_tys = tc_args
                           , dcac_arg_tys = zipEqual "dspt" (map irrelevantMult arg_tys) strict_marks
                           , dcac_co = co }
deepSplitProductType _ _ = Nothing

-----------------------------------------------------------------------------------------
-- | Binders generated by class predicates, typically for constraining tyvars (e.g. FNum)
-----------------------------------------------------------------------------------------
classBinds :: TCEmb TyCon -> SpecType -> [(Symbol, SortedReft)]
classBinds _ (RApp c ts _ _)
  | isFracCls c
  = [(symbol a, trueSortedReft FFrac) | (RVar a _) <- ts]
  | isNumCls c
  = [(symbol a, trueSortedReft FNum) | (RVar a _) <- ts]
classBinds emb (RApp c [_, _, RVar a _, t] _ _)
  | isEqual c
  = [(symbol a, rTypeSortedReft emb t)]
classBinds  emb ty@(RApp c [_, RVar a _, t] _ _)
  | isEqualityConstr ty
  = [(symbol a, rTypeSortedReft emb t)]
  | otherwise
  = notracepp ("CLASSBINDS-0: " ++ showpp c) []
classBinds _ t
  = notracepp ("CLASSBINDS-1: " ++ showpp (toType False t, isEqualityConstr t)) []

isEqualityConstr :: SpecType -> Bool
isEqualityConstr (toType False -> ty) = Ghc.isEqPred ty || Ghc.isEqPrimPred ty

--------------------------------------------------------------------------------
-- | Termination Predicates ----------------------------------------------------
--------------------------------------------------------------------------------

makeNumEnv :: (Foldable t, TyConable c) => t (RType c b t1) -> [b]
makeNumEnv = concatMap go
  where
    go (RApp c ts _ _) | isNumCls c || isFracCls c = [ a | (RVar a _) <- ts]
    go _ = []

isDecreasing :: S.HashSet TyCon -> [RTyVar] -> SpecType -> Bool
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
             -> Either (Symbol, RType RTyCon t (UReft Reft)) String
makeDecrType autoenv = mkDType autoenv [] []

mkDType :: Symbolic a
        => S.HashSet TyCon
        -> [(Symbol, Symbol, Symbol -> Expr)]
        -> [Expr]
        -> [(a, (Symbol, RType RTyCon t (UReft Reft)))]
        -> Either (Symbol, RType RTyCon t (UReft Reft)) String
mkDType autoenv xvs acc [(v, (x, t))]
  = Left ((x, ) $ t `strengthen` tr)
  where
    tr  = uTop $ Reft (vv', pOr (r:acc))
    r   = cmpLexRef xvs (v', vv', f)
    v'  = symbol v
    f   = mkDecrFun autoenv  t
    vv' = "vvRec"

mkDType autoenv xvs acc ((v, (x, t)):vxts)
  = mkDType autoenv ((v', x, f):xvs) (r:acc) vxts
  where
    r  = cmpLexRef xvs  (v', x, f)
    v' = symbol v
    f  = mkDecrFun autoenv t


mkDType _ _ _ _
  = Right "RefType.mkDType called on invalid input"

isSizeable  :: S.HashSet TyCon -> TyCon -> Bool
isSizeable autoenv tc = S.member tc autoenv --   Ghc.isAlgTyCon tc -- && Ghc.isRecursiveTyCon tc

mkDecrFun :: S.HashSet TyCon -> RType RTyCon t t1 -> Symbol -> Expr
mkDecrFun autoenv (RApp c _ _ _)
  | Just f <- szFun <$> sizeFunction (rtc_info c)
  = f
  | isSizeable autoenv $ rtc_tc c
  = \v -> F.mkEApp lenLocSymbol [F.EVar v]
mkDecrFun _ (RVar _ _)
  = EVar
mkDecrFun _ _
  = panic Nothing "RefType.mkDecrFun called on invalid input"

-- | [NOTE]: THIS IS WHERE THE TERMINATION METRIC REFINEMENTS ARE CREATED.
cmpLexRef :: [(t1, t1, t1 -> Expr)] -> (t, t, t -> Expr) -> Expr
cmpLexRef vxs (v, x, g)
  = pAnd $   PAtom Lt (g x) (g v)
         :   PAtom Ge (g x) zero
         :  [PAtom Eq (f y) (f z) | (y, z, f) <- vxs]
         ++ [PAtom Ge (f y) zero  | (y, _, f) <- vxs]
  where zero = ECon $ I 0

makeLexRefa :: [Located Expr] -> [Located Expr] -> UReft Reft
makeLexRefa es' es = uTop $ Reft (vv', PIff (EVar vv') $ pOr rs)
  where
    rs  = makeLexReft [] [] (val <$> es) (val <$> es')
    vv' = "vvRec"

makeLexReft :: [(Expr, Expr)] -> [Expr] -> [Expr] -> [Expr] -> [Expr]
makeLexReft _ acc [] []
  = acc
makeLexReft old acc (e:es) (e':es')
  = makeLexReft ((e,e'):old) (r:acc) es es'
  where
    r    = pAnd $   PAtom Lt e' e
                :   PAtom Ge e' zero
                :  [PAtom Eq o' o    | (o,o') <- old]
                ++ [PAtom Ge o' zero | (_,o') <- old]
    zero = ECon $ I 0
makeLexReft _ _ _ _
  = panic Nothing "RefType.makeLexReft on invalid input"

--------------------------------------------------------------------------------
mkTyConInfo :: TyCon -> VarianceInfo -> VarianceInfo -> Maybe SizeFun -> TyConInfo
mkTyConInfo c userTv userPv f = TyConInfo tcTv userPv f
  where
    tcTv                      = if null userTv then defTv else userTv
    defTv                     = makeTyConVariance c


--------------------------------------------------------------------------------
-- | Printing Refinement Types -------------------------------------------------
--------------------------------------------------------------------------------

instance Show RTyVar where
  show = showpp

instance PPrint (UReft r) => Show (UReft r) where
  show = showpp

instance PPrint DataDecl where
  pprintTidy k dd =
    let
      prefix = "data" <+> pprint (tycName dd) <+> ppMbSizeFun (tycSFun dd) <+> pprint (tycTyVars dd)
    in
      case tycDCons dd of
        Nothing   -> prefix
        Just cons -> prefix <+> "=" $+$ nest 4 (vcat $ [ "|" <+> pprintTidy k c | c <- cons ])

instance PPrint DataCtor where
  -- pprintTidy k (DataCtor c as _   xts Nothing)  = pprintTidy k c <+> dcolon ppVars as <+> braces (ppFields k ", " xts)
  -- pprintTidy k (DataCtor c as ths xts (Just t)) = pprintTidy k c <+> dcolon <+> ppVars as <+> ppThetas ths <+> (ppFields k " ->" xts) <+> "->" <+> pprintTidy k t
  pprintTidy k (DataCtor c as ths xts t) = pprintTidy k c <+> dcolon <+> ppVars k as <+> ppThetas ths <+> ppFields k " ->" xts <+> "->" <+> res
    where
      res         = maybe "*" (pprintTidy k) t
      ppThetas [] = empty
      ppThetas ts = parens (hcat $ punctuate ", " (pprintTidy k <$> ts)) <+> "=>"


ppVars :: (PPrint a) => Tidy -> [a] -> Doc
ppVars k as = "forall" <+> hcat (punctuate " " (F.pprintTidy k <$> as)) <+> "."

ppFields :: (PPrint k, PPrint v) => Tidy -> Doc -> [(k, v)] -> Doc
ppFields k sep' kvs = hcat $ punctuate sep' (F.pprintTidy k <$> kvs)

ppMbSizeFun :: Maybe SizeFun -> Doc
ppMbSizeFun Nothing  = ""
ppMbSizeFun (Just z) = F.pprint z

-- instance PPrint DataCtor where
  -- pprintTidy k (DataCtor c xts t) =
    -- pprintTidy k c <+> text "::" <+> (hsep $ punctuate (text "->")
                                          -- ((pprintTidy k <$> xts) ++ [pprintTidy k t]))

-- ppHack :: (?callStack :: CallStack) => a -> b
-- ppHack _ = errorstar "OOPS"

instance PPrint (RType c tv r) => Show (RType c tv r) where
  show = showpp

instance PPrint (RTProp c tv r) => Show (RTProp c tv r) where
  show = showpp


-------------------------------------------------------------------------------
-- | tyVarsPosition t returns the type variables appearing 
-- | (in positive positions, in negative positions, in undetermined positions)
-- | undetermined positions are due to type constructors and type application
-------------------------------------------------------------------------------
tyVarsPosition :: RType RTyCon tv r -> Positions tv
tyVarsPosition = go (Just True)
  where
    go p (RVar t _)        = report p t
    go p (RFun _ _ t1 t2 _)  = go (flip' p) t1 <> go p t2
    go p (RImpF _ _ t1 t2 _) = go (flip' p) t1 <> go p t2
    go p (RAllT _ t _)     = go p t
    go p (RAllP _ t)       = go p t
    go p (RApp c ts _ _)   = mconcat (zipWith go (getPosition p <$> varianceTyArgs (rtc_info c)) ts)
    go p (RAllE _ t1 t2)   = go p t1 <> go p t2
    go p (REx _ t1 t2)     = go p t1 <> go p t2
    go _ (RExprArg _)      = mempty
    go p (RAppTy t1 t2 _)  = go p t1 <> go p t2
    go p (RRTy _ _ _ t)    = go p t
    go _ (RHole _)         = mempty

    getPosition :: Maybe Bool -> Variance -> Maybe Bool
    getPosition b Contravariant = not <$> b
    getPosition b _             = b

    report Nothing v      = Pos [] [] [v]
    report (Just True) v  = Pos [v] [] []
    report (Just False) v = Pos [] [v] []
    flip' = fmap not

data Positions a = Pos {ppos :: [a], pneg ::  [a], punknown :: [a]}

instance Monoid (Positions a) where
  mempty = Pos [] [] []
instance Semigroup (Positions a) where
  (Pos x1 x2 x3) <> (Pos y1 y2 y3) = Pos (x1 ++ y1) (x2 ++ y2) (x3 ++ y3)
