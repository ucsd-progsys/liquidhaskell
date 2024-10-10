{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingVia                #-}

{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module should contain all the global type definitions and basic instances.

module Language.Haskell.Liquid.Types.RTypeOp (

  -- * Constructing & Destructing RTypes
    SpecRep
  , RTypeRep(..), fromRTypeRep, toRTypeRep
  , mkArrow, bkArrowDeep, bkArrow, safeBkArrow
  , mkUnivs, bkUniv, bkClass, bkUnivClass, bkUnivClass'
  , rFun, rFun', rCls, rRCls, rFunDebug
  , classRFInfoType

  -- * Traversing `RType`
  , efoldReft, foldReft, foldReft'
  , emapReft, mapReft, mapReftM, mapPropM
  , mapExprReft
  , mapBot, mapBind, mapRFInfo
  , foldRType

  -- * Converting To and From Sort
  , ofRSort, toRSort
  , rTypeValueVar
  , rTypeReft
  , stripRTypeBase
  , topRTypeBase

  -- * Some tests on RTypes
  , isBase
  , isFunTy
  , isTrivial
  , hasHoleTy

  -- * Scoping Info
  , BScope

  -- * Misc
  , addInvCond
  , insertsSEnv
  )
  where

import qualified Liquid.GHC.API as Ghc
import           Prelude                          hiding  (error)
import qualified Prelude

import           Control.Monad                          (liftM2, liftM3, liftM4, void)
import           Language.Fixpoint.Misc

import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Types (Expr, Symbol)

import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Misc


-----------------------------------------------------------------------------
-- | Information about scope Binders Scope in
-----------------------------------------------------------------------------
{- In types with base refinement, e.g., {out:T {inner:a | ri} | ro }
If BScope = True , then the outer binder out is     in scope on ri
If BScope = False, then the outer binder out is not in scope on ri
-}

type BScope = Bool

--------------------------------------------------------------------------------
-- | Constructor and Destructors for RTypes ------------------------------------
--------------------------------------------------------------------------------
type RRep        = RTypeRep RTyCon RTyVar
type SpecRep     = RRep      RReft

data RTypeRep c tv r = RTypeRep
  { ty_vars   :: [(RTVar tv (RType c tv ()), r)]
  , ty_preds  :: [PVar (RType c tv ())]
  , ty_binds  :: [Symbol]
  , ty_info   :: [RFInfo]
  , ty_refts  :: [r]
  , ty_args   :: [RType c tv r]
  , ty_res    :: RType c tv r
  }

fromRTypeRep :: RTypeRep c tv r -> RType c tv r
fromRTypeRep RTypeRep{..}
  = mkArrow ty_vars ty_preds arrs ty_res
  where
    arrs = safeZip4WithError ("fromRTypeRep: " ++ show (length ty_binds, length ty_info, length ty_args, length ty_refts)) ty_binds ty_info ty_args ty_refts

classRFInfoType :: Bool -> RType c tv r -> RType c tv r
classRFInfoType b = fromRTypeRep .
                    (\trep@RTypeRep{..} -> trep{ty_info = map (\i -> i{permitTC = pure b}) ty_info}) .
                    toRTypeRep

--------------------------------------------------------------------------------
toRTypeRep           :: RType c tv r -> RTypeRep c tv r
--------------------------------------------------------------------------------
toRTypeRep t         = RTypeRep αs πs xs is rs ts t''
  where
    (αs, πs, t') = bkUniv t
    ((xs, is, ts, rs), t'') = bkArrow t'

mkArrow :: [(RTVar tv (RType c tv ()), r)]
        -> [PVar (RType c tv ())]
        -> [(Symbol, RFInfo, RType c tv r, r)]
        -> RType c tv r
        -> RType c tv r
mkArrow αs πs zts = mkUnivs αs πs . mkRFuns zts
  where
    mkRFuns xts t = foldr (\(b,i,t1,r) t2 -> RFun b i t1 t2 r) t xts

-- Do I need to keep track of implicits here too?
bkArrowDeep :: RType t t1 a -> ([Symbol], [RFInfo], [RType t t1 a], [a], RType t t1 a)
bkArrowDeep (RAllT _ t _)   = bkArrowDeep t
bkArrowDeep (RAllP _ t)     = bkArrowDeep t
bkArrowDeep (RFun x i t t' r) = let (xs, is, ts, rs, t'') = bkArrowDeep t' in
                                (x:xs, i:is, t:ts, r:rs, t'')
bkArrowDeep t               = ([], [], [], [], t)

bkArrow :: RType t t1 a -> ( ([Symbol], [RFInfo], [RType t t1 a], [a])
                           , RType t t1 a )
bkArrow t                = ((xs,is,ts,rs),t')
  where
    (xs, is, ts, rs, t') = bkFun t

bkFun :: RType t t1 a -> ([Symbol], [RFInfo], [RType t t1 a], [a], RType t t1 a)
bkFun (RFun x i t t' r) = let (xs, is, ts, rs, t'') = bkFun t' in
                          (x:xs, i:is, t:ts, r:rs, t'')
bkFun t                 = ([], [], [], [], t)

safeBkArrow ::(F.PPrint (RType t t1 a))
            => RType t t1 a -> ( ([Symbol], [RFInfo], [RType t t1 a], [a])
                               , RType t t1 a )
safeBkArrow t@RAllT {} = Prelude.error {- panic Nothing -} $ "safeBkArrow on RAllT" ++ F.showpp t
safeBkArrow (RAllP _ _)     = Prelude.error {- panic Nothing -} "safeBkArrow on RAllP"
safeBkArrow t               = bkArrow t

mkUnivs :: (Foldable t, Foldable t1)
        => t  (RTVar tv (RType c tv ()), r)
        -> t1 (PVar (RType c tv ()))
        -> RType c tv r
        -> RType c tv r
mkUnivs αs πs rt = foldr (\(a,r) t -> RAllT a t r) (foldr RAllP rt πs) αs

bkUnivClass :: SpecType -> ([(SpecRTVar, RReft)],[PVar RSort], [(RTyCon, [SpecType])], SpecType )
bkUnivClass t        = (as, ps, cs, t2)
  where
    (as, ps, t1) = bkUniv  t
    (cs, t2)     = bkClass t1


bkUniv :: RType tv c r -> ([(RTVar c (RType tv c ()), r)], [PVar (RType tv c ())], RType tv c r)
bkUniv (RAllT α t r) = let (αs, πs, t') = bkUniv t in ((α, r):αs, πs, t')
bkUniv (RAllP π t)   = let (αs, πs, t') = bkUniv t in (αs, π:πs, t')
bkUniv t             = ([], [], t)


-- bkFun :: RType t t1 a -> ([Symbol], [RType t t1 a], [a], RType t t1 a)
-- bkFun (RFun x t t' r) = let (xs, ts, rs, t'') = bkFun t'  in (x:xs, t:ts, r:rs, t'')
-- bkFun t               = ([], [], [], t)

bkUnivClass' :: SpecType ->
  ([(SpecRTVar, RReft)], [PVar RSort], [(Symbol, SpecType, RReft)], SpecType)
bkUnivClass' t = (as, ps, zip3 bs ts rs, t2)
  where
    (as, ps, t1) = bkUniv  t
    (bs, ts, rs, t2)     = bkClass' t1

bkClass' :: TyConable t => RType t t1 a -> ([Symbol], [RType t t1 a], [a], RType t t1 a)
bkClass' (RFun x _ t@(RApp c _ _ _) t' r)
  | isClass c
  = let (xs, ts, rs, t'') = bkClass' t' in (x:xs, t:ts, r:rs, t'')
bkClass' (RRTy e r o t)
  = let (xs, ts, rs, t'') = bkClass' t in (xs, ts, rs, RRTy e r o t'')
bkClass' t
  = ([], [],[],t)

bkClass :: (F.PPrint c, TyConable c) => RType c tv r -> ([(c, [RType c tv r])], RType c tv r)
bkClass (RFun _ _ (RApp c t _ _) t' _)
  | F.notracepp ("IS-CLASS: " ++ F.showpp c) $ isClass c
  = let (cs, t'') = bkClass t' in ((c, t):cs, t'')
bkClass (RRTy e r o t)
  = let (cs, t') = bkClass t in (cs, RRTy e r o t')
bkClass t
  = ([], t)

rFun :: Monoid r => Symbol -> RType c tv r -> RType c tv r -> RType c tv r
rFun b t t' = RFun b defRFInfo t t' mempty

rFun' :: Monoid r => RFInfo -> Symbol -> RType c tv r -> RType c tv r -> RType c tv r
rFun' i b t t' = RFun b i t t' mempty

rFunDebug :: Monoid r => Symbol -> RType c tv r -> RType c tv r -> RType c tv r
rFunDebug b t t' = RFun b (classRFInfo True) t t' mempty

rCls :: Monoid r => Ghc.TyCon -> [RType RTyCon tv r] -> RType RTyCon tv r
rCls c ts   = RApp (RTyCon c [] defaultTyConInfo) ts [] mempty

rRCls :: Monoid r => c -> [RType c tv r] -> RType c tv r
rRCls rc ts = RApp rc ts [] mempty

addInvCond :: SpecType -> RReft -> SpecType
addInvCond t r'
  | isTauto $ ur_reft r' -- null rv
  = t
  | otherwise
  = fromRTypeRep $ trep {ty_res = RRTy [(x', tbd)] r OInv tbd}
  where
    trep = toRTypeRep t
    tbd  = ty_res trep
    r    = r' {ur_reft = F.Reft (v, rx)}
    su   = (v, F.EVar x')
    x'   = "xInv"
    rx   = F.PIff (F.EVar v) $ F.subst1 rv su
    F.Reft(v, rv) = ur_reft r'


instance (Reftable r, TyConable c) => F.Subable (RTProp c tv r) where
  syms (RProp  ss r)     = (fst <$> ss) ++ F.syms r

  subst su (RProp ss (RHole r)) = RProp ss (RHole (F.subst su r))
  subst su (RProp  ss t) = RProp ss (F.subst su <$> t)

  substf f (RProp ss (RHole r)) = RProp ss (RHole (F.substf f r))
  substf f (RProp  ss t) = RProp ss (F.substf f <$> t)

  substa f (RProp ss (RHole r)) = RProp ss (RHole (F.substa f r))
  substa f (RProp  ss t) = RProp ss (F.substa f <$> t)


instance (F.Subable r, Reftable r, TyConable c) => F.Subable (RType c tv r) where
  syms        = foldReft False (\_ r acc -> F.syms r ++ acc) []
  -- 'substa' will substitute bound vars
  substa f    = emapExprArg (\_ -> F.substa f) []      . mapReft  (F.substa f)
  -- 'substf' will NOT substitute bound vars
  substf f    = emapExprArg (\_ -> F.substf f) []      . emapReft (F.substf . F.substfExcept f) []
  subst su    = emapExprArg (\_ -> F.subst su) []      . emapReft (F.subst  . F.substExcept su) []
  subst1 t su = emapExprArg (\_ e -> F.subst1 e su) [] $ emapReft (\xs r -> F.subst1Except xs r su) [] t


--------------------------------------------------------------------------------
-- | Visitors ------------------------------------------------------------------
--------------------------------------------------------------------------------
mapExprReft :: (Symbol -> Expr -> Expr) -> RType c tv RReft -> RType c tv RReft
mapExprReft f = mapReft g
  where
    g (MkUReft (F.Reft (x, e)) p) = MkUReft (F.Reft (x, f x e)) p

-- const False (not dropping dict) is probably fine since there will not be refinement on
-- dictionaries
isTrivial :: (Reftable r, TyConable c) => RType c tv r -> Bool
isTrivial = foldReft False (\_ r b -> isTauto r && b) True

mapReft ::  (r1 -> r2) -> RType c tv r1 -> RType c tv r2
mapReft f = emapReft (const f) []

emapReft ::  ([Symbol] -> r1 -> r2) -> [Symbol] -> RType c tv r1 -> RType c tv r2
emapReft f γ (RVar α r)        = RVar  α (f γ r)
emapReft f γ (RAllT α t r)     = RAllT α (emapReft f γ t) (f γ r)
emapReft f γ (RAllP π t)       = RAllP π (emapReft f γ t)
emapReft f γ (RFun x i t t' r) = RFun  x i (emapReft f γ t) (emapReft f (x:γ) t') (f (x:γ) r)
emapReft f γ (RApp c ts rs r)  = RApp  c (emapReft f γ <$> ts) (emapRef f γ <$> rs) (f γ r)
emapReft f γ (RAllE z t t')    = RAllE z (emapReft f γ t) (emapReft f γ t')
emapReft f γ (REx z t t')      = REx   z (emapReft f γ t) (emapReft f γ t')
emapReft _ _ (RExprArg e)      = RExprArg e
emapReft f γ (RAppTy t t' r)   = RAppTy (emapReft f γ t) (emapReft f γ t') (f γ r)
emapReft f γ (RRTy e r o t)    = RRTy  (mapSnd (emapReft f γ) <$> e) (f γ r) o (emapReft f γ t)
emapReft f γ (RHole r)         = RHole (f γ r)

emapRef :: ([Symbol] -> t -> s) ->  [Symbol] -> RTProp c tv t -> RTProp c tv s
emapRef  f γ (RProp s (RHole r))  = RProp s $ RHole (f γ r)
emapRef  f γ (RProp s t)         = RProp s $ emapReft f γ t

emapExprArg :: ([Symbol] -> Expr -> Expr) -> [Symbol] -> RType c tv r -> RType c tv r
emapExprArg f = go
  where
    go _ t@RVar{}          = t
    go _ t@RHole{}         = t
    go γ (RAllT α t r)     = RAllT α (go γ t) r
    go γ (RAllP π t)       = RAllP π (go γ t)
    go γ (RFun x i t t' r) = RFun  x i (go γ t) (go (x:γ) t') r
    go γ (RApp c ts rs r)  = RApp  c (go γ <$> ts) (mo γ <$> rs) r
    go γ (RAllE z t t')    = RAllE z (go γ t) (go γ t')
    go γ (REx z t t')      = REx   z (go γ t) (go γ t')
    go γ (RExprArg e)      = RExprArg (f γ <$> F.notracepp "RExprArg" e) -- <---- actual substitution
    go γ (RAppTy t t' r)   = RAppTy (go γ t) (go γ t') r
    go γ (RRTy e r o t)    = RRTy  (mapSnd (go γ) <$> e) r o (go γ t)

    mo _ t@(RProp _ RHole{}) = t
    mo γ (RProp s t)         = RProp s (go γ t)

foldRType :: (acc -> RType c tv r -> acc) -> acc -> RType c tv r -> acc
foldRType f = go
  where
    step a t                = go (f a t) t
    prep a (RProp _ RHole{}) = a
    prep a (RProp _ t)      = step a t
    go a RVar{}             = a
    go a RHole{}            = a
    go a RExprArg{}         = a
    go a (RAllT _ t _)      = step a t
    go a (RAllP _ t)        = step a t
    go a (RFun _ _ t t' _)  = foldl' step a [t, t']
    go a (RAllE _ t t')     = foldl' step a [t, t']
    go a (REx _ t t')       = foldl' step a [t, t']
    go a (RAppTy t t' _)    = foldl' step a [t, t']
    go a (RApp _ ts rs _)   = foldl' prep (foldl' step a ts) rs
    go a (RRTy e _ _ t)     = foldl' step a (t : (snd <$> e))

------------------------------------------------------------------------------------------------------
-- isBase' x t = traceShow ("isBase: " ++ showpp x) $ isBase t
-- same as GhcMisc isBaseType

-- isBase :: RType a -> Bool

-- set all types to basic types, haskell `tx -> t` is translated to Arrow tx t
-- isBase _ = True

isBase :: RType t t1 t2 -> Bool
isBase (RAllT _ t _)    = isBase t
isBase (RAllP _ t)      = isBase t
isBase (RVar _ _)       = True
isBase (RApp _ ts _ _)  = all isBase ts
isBase RFun{}           = False
isBase (RAppTy t1 t2 _) = isBase t1 && isBase t2
isBase (RRTy _ _ _ t)   = isBase t
isBase (RAllE _ _ t)    = isBase t
isBase (REx _ _ t)      = isBase t
isBase _                = False

hasHoleTy :: RType t t1 t2 -> Bool
hasHoleTy (RVar _ _)        = False
hasHoleTy (RAllT _ t _)     = hasHoleTy t
hasHoleTy (RAllP _ t)       = hasHoleTy t
hasHoleTy (RFun _ _ t t' _) = hasHoleTy t || hasHoleTy t'
hasHoleTy (RApp _ ts _ _)   = any hasHoleTy ts
hasHoleTy (RAllE _ t t')    = hasHoleTy t || hasHoleTy t'
hasHoleTy (REx _ t t')      = hasHoleTy t || hasHoleTy t'
hasHoleTy (RExprArg _)      = False
hasHoleTy (RAppTy t t' _)   = hasHoleTy t || hasHoleTy t'
hasHoleTy (RHole _)         = True
hasHoleTy (RRTy xts _ _ t)  = hasHoleTy t || any hasHoleTy (snd <$> xts)

isFunTy :: RType t t1 t2 -> Bool
isFunTy (RAllE _ _ t)    = isFunTy t
isFunTy (RAllT _ t _)    = isFunTy t
isFunTy (RAllP _ t)      = isFunTy t
isFunTy RFun{}           = True
isFunTy _                = False

mapReftM :: (Monad m) => (r1 -> m r2) -> RType c tv r1 -> m (RType c tv r2)
mapReftM f (RVar α r)        = fmap   (RVar  α)  (f r)
mapReftM f (RAllT α t r)     = liftM2 (RAllT α)  (mapReftM f t)         (f r)
mapReftM f (RAllP π t)       = fmap   (RAllP π)  (mapReftM f t)
mapReftM f (RFun x i t t' r) = liftM3 (RFun x i) (mapReftM f t)         (mapReftM f t')       (f r)
mapReftM f (RApp c ts rs r)  = liftM3 (RApp  c)  (mapM (mapReftM f) ts) (mapM (mapRefM f) rs) (f r)
mapReftM f (RAllE z t t')    = liftM2 (RAllE z)  (mapReftM f t)         (mapReftM f t')
mapReftM f (REx z t t')      = liftM2 (REx z)    (mapReftM f t)         (mapReftM f t')
mapReftM _ (RExprArg e)      = return $ RExprArg e
mapReftM f (RAppTy t t' r)   = liftM3 RAppTy (mapReftM f t) (mapReftM f t') (f r)
mapReftM f (RHole r)         = fmap   RHole      (f r)
mapReftM f (RRTy xts r o t)  = liftM4 RRTy (mapM (mapSndM (mapReftM f)) xts) (f r) (return o) (mapReftM f t)

mapRefM  :: (Monad m) => (t -> m s) -> RTProp c tv t -> m (RTProp c tv s)
mapRefM  f (RProp s t)        = fmap    (RProp s)      (mapReftM f t)

mapPropM :: (Monad m) => (RTProp c tv r -> m (RTProp c tv r)) -> RType c tv r -> m (RType c tv r)
mapPropM _ (RVar α r)        = return $ RVar  α r
mapPropM f (RAllT α t r)     = liftM2 (RAllT α)   (mapPropM f t)          (return r)
mapPropM f (RAllP π t)       = fmap   (RAllP π)   (mapPropM f t)
mapPropM f (RFun x i t t' r) = liftM3 (RFun x i)  (mapPropM f t)          (mapPropM f t') (return r)
mapPropM f (RApp c ts rs r)  = liftM3 (RApp  c)   (mapM (mapPropM f) ts)  (mapM f rs)     (return r)
mapPropM f (RAllE z t t')    = liftM2 (RAllE z)   (mapPropM f t)          (mapPropM f t')
mapPropM f (REx z t t')      = liftM2 (REx z)     (mapPropM f t)          (mapPropM f t')
mapPropM _ (RExprArg e)      = return $ RExprArg e
mapPropM f (RAppTy t t' r)   = liftM3 RAppTy (mapPropM f t) (mapPropM f t') (return r)
mapPropM _ (RHole r)         = return $ RHole r
mapPropM f (RRTy xts r o t)  = liftM4 RRTy (mapM (mapSndM (mapPropM f)) xts) (return r) (return o) (mapPropM f t)


--------------------------------------------------------------------------------
-- foldReft :: (Reftable r, TyConable c) => (r -> a -> a) -> a -> RType c tv r -> a
--------------------------------------------------------------------------------
-- foldReft f = efoldReft (\_ _ -> []) (\_ -> ()) (\_ _ -> f) (\_ γ -> γ) emptyF.SEnv

--------------------------------------------------------------------------------
foldReft :: (Reftable r, TyConable c) => BScope -> (F.SEnv (RType c tv r) -> r -> a -> a) -> a -> RType c tv r -> a
--------------------------------------------------------------------------------
foldReft bsc f = foldReft'  (\_ _ -> False) bsc id (\γ _ -> f γ)

--------------------------------------------------------------------------------
foldReft' :: (Reftable r, TyConable c)
          => (Symbol -> RType c tv r -> Bool)
          -> BScope
          -> (RType c tv r -> b)
          -> (F.SEnv b -> Maybe (RType c tv r) -> r -> a -> a)
          -> a -> RType c tv r -> a
--------------------------------------------------------------------------------
foldReft' logicBind bsc g f
  = efoldReft logicBind bsc
              (\_ _ -> [])
              (const [])
              g
              (\γ t r z -> f γ t r z)
              (\_ γ -> γ)
              F.emptySEnv

tyVarIsVal :: RTVar tv s -> Bool
tyVarIsVal = rtvinfoIsVal . ty_var_info

rtvinfoIsVal :: RTVInfo s -> Bool
rtvinfoIsVal RTVNoInfo{} = False
rtvinfoIsVal RTVInfo{..} = rtv_is_val

-- efoldReft :: Reftable r =>(p -> [RType c tv r] -> [(Symbol, a)])-> (RType c tv r -> a)-> (SEnv a -> Maybe (RType c tv r) -> r -> c1 -> c1)-> SEnv a-> c1-> RType c tv r-> c1
efoldReft :: (Reftable r, TyConable c)
          => (Symbol -> RType c tv r -> Bool)
          -> BScope
          -> (c  -> [RType c tv r] -> [(Symbol, a)])
          -> (RTVar tv (RType c tv ()) -> [(Symbol, a)])
          -> (RType c tv r -> a)
          -> (F.SEnv a -> Maybe (RType c tv r) -> r -> b -> b)
          -> (PVar (RType c tv ()) -> F.SEnv a -> F.SEnv a)
          -> F.SEnv a
          -> b
          -> RType c tv r
          -> b
efoldReft logicBind bsc cb dty g f fp = go
  where
    -- folding over RType
    go γ z me@(RVar _ r)                = f γ (Just me) r z
    go γ z me@(RAllT a t r)
       | tyVarIsVal a                   = f γ (Just me) r (go (insertsSEnv γ (dty a)) z t)
       | otherwise                      = f γ (Just me) r (go γ z t)
    go γ z (RAllP p t)                  = go (fp p γ) z t
    go γ z me@(RFun _ RFInfo{permitTC = permitTC} (RApp c ts _ _) t' r)
       | (if permitTC == Just True then isEmbeddedDict else isClass)
         c  = f γ (Just me) r (go (insertsSEnv γ (cb c ts)) (go' γ z ts) t')
    go γ z me@(RFun x _ t t' r)
       | logicBind x t                  = f γ (Just me) r (go γ' (go γ z t) t')
       | otherwise                      = f γ (Just me) r (go γ  (go γ z t) t')
       where
         γ'                             = insertSEnv x (g t) γ
    go γ z me@(RApp _ ts rs r)          = f γ (Just me) r (ho' γ (go' γ' z ts) rs)
       where γ' = if bsc then insertSEnv (rTypeValueVar me) (g me) γ else γ

    go γ z (RAllE x t t')               = go (insertSEnv x (g t) γ) (go γ z t) t'
    go γ z (REx x t t')                 = go (insertSEnv x (g t) γ) (go γ z t) t'
    go γ z me@(RRTy [] r _ t)           = f γ (Just me) r (go γ z t)
    go γ z me@(RRTy xts r _ t)          = f γ (Just me) r (go γ (go γ z (envtoType xts)) t)
    go γ z me@(RAppTy t t' r)           = f γ (Just me) r (go γ (go γ z t) t')
    go _ z (RExprArg _)                 = z
    go γ z me@(RHole r)                 = f γ (Just me) r z

    -- folding over Ref
    ho  γ z (RProp ss (RHole r))       = f (insertsSEnv γ (mapSnd (g . ofRSort) <$> ss)) Nothing r z
    ho  γ z (RProp ss t)               = go (insertsSEnv γ (mapSnd (g . ofRSort) <$> ss)) z t

    -- folding over [RType]
    go' γ z ts                 = foldr (flip $ go γ) z ts

    -- folding over [Ref]
    ho' γ z rs                 = foldr (flip $ ho γ) z rs

    envtoType xts = foldr (\(x,t1) t2 -> rFun x t1 t2) (snd $ last xts) (init xts)

mapRFInfo :: (RFInfo -> RFInfo) -> RType c tv r -> RType c tv r
mapRFInfo f (RAllT α t r)     = RAllT α (mapRFInfo f t) r
mapRFInfo f (RAllP π t)       = RAllP π (mapRFInfo f t)
mapRFInfo f (RFun x i t t' r) = RFun x (f i) (mapRFInfo f t) (mapRFInfo f t') r
mapRFInfo f (RAppTy t t' r)   = RAppTy (mapRFInfo f t) (mapRFInfo f t') r
mapRFInfo f (RApp c ts rs r)  = RApp c (mapRFInfo f <$> ts) (mapRFInfoRef f <$> rs) r
mapRFInfo f (REx b t1 t2)     = REx b  (mapRFInfo f t1) (mapRFInfo f t2)
mapRFInfo f (RAllE b t1 t2)   = RAllE b (mapRFInfo f t1) (mapRFInfo f t2)
mapRFInfo f (RRTy e r o t)    = RRTy (mapSnd (mapRFInfo f) <$> e) r o (mapRFInfo f t)
mapRFInfo _ t'                = t'

mapRFInfoRef :: (RFInfo -> RFInfo)
          -> Ref τ (RType c tv r) -> Ref τ (RType c tv r)
mapRFInfoRef _ (RProp s (RHole r)) = RProp s $ RHole r
mapRFInfoRef f (RProp s t)    = RProp  s $ mapRFInfo f t

mapBot :: (RType c tv r -> RType c tv r) -> RType c tv r -> RType c tv r
mapBot f (RAllT α t r)     = RAllT α (mapBot f t) r
mapBot f (RAllP π t)       = RAllP π (mapBot f t)
mapBot f (RFun x i t t' r) = RFun x i (mapBot f t) (mapBot f t') r
mapBot f (RAppTy t t' r)   = RAppTy (mapBot f t) (mapBot f t') r
mapBot f (RApp c ts rs r)  = f $ RApp c (mapBot f <$> ts) (mapBotRef f <$> rs) r
mapBot f (REx b t1 t2)     = REx b  (mapBot f t1) (mapBot f t2)
mapBot f (RAllE b t1 t2)   = RAllE b  (mapBot f t1) (mapBot f t2)
mapBot f (RRTy e r o t)    = RRTy (mapSnd (mapBot f) <$> e) r o (mapBot f t)
mapBot f t'                = f t'

mapBotRef :: (RType c tv r -> RType c tv r)
          -> Ref τ (RType c tv r) -> Ref τ (RType c tv r)
mapBotRef _ (RProp s (RHole r)) = RProp s $ RHole r
mapBotRef f (RProp s t)         = RProp s $ mapBot f t

mapBind :: (Symbol -> Symbol) -> RType c tv r -> RType c tv r
mapBind f (RAllT α t r)      = RAllT α (mapBind f t) r
mapBind f (RAllP π t)        = RAllP π (mapBind f t)
mapBind f (RFun b i t1 t2 r) = RFun (f b) i (mapBind f t1) (mapBind f t2) r
mapBind f (RApp c ts rs r)   = RApp c (mapBind f <$> ts) (mapBindRef f <$> rs) r
mapBind f (RAllE b t1 t2)    = RAllE  (f b) (mapBind f t1) (mapBind f t2)
mapBind f (REx b t1 t2)      = REx    (f b) (mapBind f t1) (mapBind f t2)
mapBind _ (RVar α r)         = RVar α r
mapBind _ (RHole r)          = RHole r
mapBind f (RRTy e r o t)     = RRTy e r o (mapBind f t)
mapBind _ (RExprArg e)       = RExprArg e
mapBind f (RAppTy t t' r)    = RAppTy (mapBind f t) (mapBind f t') r

mapBindRef :: (Symbol -> Symbol)
           -> Ref τ (RType c tv r) -> Ref τ (RType c tv r)
mapBindRef f (RProp s (RHole r)) = RProp (mapFst f <$> s) (RHole r)
mapBindRef f (RProp s t)         = RProp (mapFst f <$> s) $ mapBind f t


--------------------------------------------------
ofRSort ::  Reftable r => RType c tv () -> RType c tv r
ofRSort = fmap mempty

toRSort :: RType c tv r -> RType c tv ()
toRSort = stripAnnotations . mapBind (const F.dummySymbol) . void

stripAnnotations :: RType c tv r -> RType c tv r
stripAnnotations (RAllT α t r)     = RAllT α (stripAnnotations t) r
stripAnnotations (RAllP _ t)       = stripAnnotations t
stripAnnotations (RAllE _ _ t)     = stripAnnotations t
stripAnnotations (REx _ _ t)       = stripAnnotations t
stripAnnotations (RFun x i t t' r) = RFun x i (stripAnnotations t) (stripAnnotations t') r
stripAnnotations (RAppTy t t' r)   = RAppTy (stripAnnotations t) (stripAnnotations t') r
stripAnnotations (RApp c ts rs r)  = RApp c (stripAnnotations <$> ts) (stripAnnotationsRef <$> rs) r
stripAnnotations (RRTy _ _ _ t)    = stripAnnotations t
stripAnnotations t                 = t

stripAnnotationsRef :: Ref τ (RType c tv r) -> Ref τ (RType c tv r)
stripAnnotationsRef (RProp s (RHole r)) = RProp s (RHole r)
stripAnnotationsRef (RProp s t)         = RProp s $ stripAnnotations t

insertSEnv :: F.Symbol -> a -> F.SEnv a -> F.SEnv a
insertSEnv = F.insertSEnv

insertsSEnv :: F.SEnv a -> [(Symbol, a)] -> F.SEnv a
insertsSEnv  = foldr (\(x, t) γ -> insertSEnv x t γ)

rTypeValueVar :: (Reftable r) => RType c tv r -> Symbol
rTypeValueVar t = vv where F.Reft (vv,_) =  rTypeReft t

rTypeReft :: (Reftable r) => RType c tv r -> F.Reft
rTypeReft = maybe F.trueReft toReft . stripRTypeBase

-- stripRTypeBase ::  RType a -> Maybe a
stripRTypeBase :: RType c tv r -> Maybe r
stripRTypeBase (RApp _ _ _ x)   = Just x
stripRTypeBase (RVar _ x)       = Just x
stripRTypeBase (RFun _ _ _ _ x) = Just x
stripRTypeBase (RAppTy _ _ x)   = Just x
stripRTypeBase (RAllT _ _ x)    = Just x
stripRTypeBase _                = Nothing

topRTypeBase :: (Reftable r) => RType c tv r -> RType c tv r
topRTypeBase = mapRBase top

mapRBase :: (r -> r) -> RType c tv r -> RType c tv r
mapRBase f (RApp c ts rs r)   = RApp c ts rs $ f r
mapRBase f (RVar a r)         = RVar a $ f r
mapRBase f (RFun x i t1 t2 r) = RFun x i t1 t2 $ f r
mapRBase f (RAppTy t1 t2 r)   = RAppTy t1 t2 $ f r
mapRBase _ t                  = t
