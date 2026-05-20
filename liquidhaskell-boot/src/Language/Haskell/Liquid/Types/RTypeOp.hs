{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ScopedTypeVariables        #-}

{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module should contain all the global type definitions and basic instances.

module Language.Haskell.Liquid.Types.RTypeOp (

  -- * Constructing & Destructing RTypes
    SpecRep
  , RTypeRep, RTypeRepV, RTypeRepBV(..), fromRTypeRep, toRTypeRep
  , mkArrow, bkArrowDeep, bkArrow, safeBkArrow
  , mkUnivs, bkUniv, bkClass, bkUnivClass, bkUnivClass'
  , rFun, rFun', rCls, rRCls, rFunDebug
  , classRFInfoType

  -- * Traversing `RType`
  , efoldReft, foldReft, foldReft'
  , emapReft, mapReft, mapReftM, mapPropM
  , emapReftM, emapRefM
  , mapExprReft
  , mapBot, mapBind, mapRFInfo
  , foldRType
  , emapFReftM
  , mapRTypeV
  , mapRTypeVM
  , mapDataDeclV
  , mapDataDeclVM
  , mapRBase
  , emapDataDeclM
  , emapDataCtorTyM
  , emapBareTypeVM
  , parsedToBareType

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

import           Control.Monad                          (liftM2, liftM3, liftM4)
import           Data.Bifunctor (bimap)
import           Data.Coerce (coerce)
import           Data.Hashable (Hashable)
import qualified Data.HashSet as S
import qualified Data.List as List

import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Types (ExprBV, Symbol)

import           Language.Haskell.Liquid.Types.DataDecl
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names
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

type RTypeRep = RTypeRepV Symbol
type RTypeRepV = RTypeRepBV Symbol
data RTypeRepBV b v c tv r = RTypeRep
  { ty_vars   :: [(RTVar b v c tv, r)]
  , ty_preds  :: [PVarBV b v (RTypeBV b v c tv (NoReftBV b v))]
  , ty_binds  :: [b]
  , ty_info   :: [RFInfo]
  , ty_refts  :: [r]
  , ty_args   :: [RTypeBV b v c tv r]
  , ty_res    :: RTypeBV b v c tv r
  }

fromRTypeRep :: RTypeRepBV b v c tv r -> RTypeBV b v c tv r
fromRTypeRep RTypeRep{..}
  = mkArrow ty_vars ty_preds arrs ty_res
  where
    arrs = safeZip4WithError ("fromRTypeRep: " ++ show (length ty_binds, length ty_info, length ty_args, length ty_refts)) ty_binds ty_info ty_args ty_refts

classRFInfoType :: Bool -> RType c tv r -> RType c tv r
classRFInfoType b = fromRTypeRep .
                    (\trep@RTypeRep{..} -> trep{ty_info = map (\i -> i{permitTC = pure b}) ty_info}) .
                    toRTypeRep

--------------------------------------------------------------------------------
toRTypeRep           :: RTypeBV b v c tv r -> RTypeRepBV b v c tv r
--------------------------------------------------------------------------------
toRTypeRep t         = RTypeRep αs πs xs is rs ts t''
  where
    (αs, πs, t') = bkUniv t
    ((xs, is, ts, rs), t'') = bkArrow t'

mkArrow :: [(RTVar b v c tv, r)]
        -> [PVarBV b v (RTypeBV b v c tv (NoReftBV b v))]
        -> [(b, RFInfo, RTypeBV b v c tv r, r)]
        -> RTypeBV b v c tv r
        -> RTypeBV b v c tv r
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

bkArrow :: RTypeBV b v t t1 a -> ( ([b], [RFInfo], [RTypeBV b v t t1 a], [a])
                                 , RTypeBV b v t t1 a )
bkArrow t                = ((xs,is,ts,rs),t')
  where
    (xs, is, ts, rs, t') = bkFun t

bkFun :: RTypeBV b v t t1 a -> ([b], [RFInfo], [RTypeBV b v t t1 a], [a], RTypeBV b v t t1 a)
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
        => t  (RTVar b v c tv, r)
        -> t1 (PVarBV b v (RTypeBV b v c tv (NoReftBV b v)))
        -> RTypeBV b v c tv r
        -> RTypeBV b v c tv r
mkUnivs αs πs rt = foldr (\(a,r) t -> RAllT a t r) (foldr RAllP rt πs) αs

bkUnivClass :: SpecType -> ([(SpecRTVar, RReft)],[PVar RSort], [(RTyCon, [SpecType])], SpecType )
bkUnivClass t        = (as, ps, cs, t2)
  where
    (as, ps, t1) = bkUniv  t
    (cs, t2)     = bkClass t1


bkUniv :: RTypeBV b v c tv r -> ([(RTVar b v c tv, r)], [PVarBV b v (RTypeBV b v c tv (NoReftBV b v))], RTypeBV b v c tv r)
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

bkClass :: (F.PPrint c, TyConable c) => RTypeBV b v c tv r -> ([(c, [RTypeBV b v c tv r])], RTypeBV b v c tv r)
bkClass (RFun _ _ (RApp c t _ _) t' _)
  | F.notracepp ("IS-CLASS: " ++ F.showpp c) $ isClass c
  = let (cs, t'') = bkClass t' in ((c, t):cs, t'')
bkClass (RRTy e r o t)
  = let (cs, t') = bkClass t in (cs, RRTy e r o t')
bkClass t
  = ([], t)

rFun :: IsReft r => b -> RTypeBV b v c tv r -> RTypeBV b v c tv r -> RTypeBV b v c tv r
rFun b t t' = RFun b defRFInfo t t' trueReft

rFun' :: IsReft r => RFInfo -> Symbol -> RType c tv r -> RType c tv r -> RType c tv r
rFun' i b t t' = RFun b i t t' trueReft

rFunDebug :: IsReft r => Symbol -> RType c tv r -> RType c tv r -> RType c tv r
rFunDebug b t t' = RFun b (classRFInfo True) t t' trueReft

rCls :: IsReft r => Ghc.TyCon -> [RType RTyCon tv r] -> RType RTyCon tv r
rCls c ts   = RApp (RTyCon c [] defaultTyConInfo) ts [] trueReft

rRCls :: IsReft r => c -> [RType c tv r] -> RType c tv r
rRCls rc ts = RApp rc ts [] trueReft

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


instance ( IsReft r
         , F.Subable r
         , F.Subable t
         , TyConable c
         , F.Binder v
         , F.Refreshable v
         , F.Variable r ~ v
         , F.Variable t ~ v
         , ReftBind r ~ v
         ) =>
         F.Subable (RefB v (RTypeBV v v c tv r) t) where
  type Variable (RefB v (RTypeBV v v c tv r) t) = v
  syms (RProp ss r) =
    let (bs, tss) =
          List.mapAccumL
            (\bs0 (b, tb) -> (S.insert b bs0, F.syms tb `S.difference` bs0))
            S.empty
            ss
     in
        S.unions $ (F.syms r `S.difference` bs) : tss

  substr ns su (RProp  ss t) = RProp ss (F.substr ns su t)

  subst su (RProp  ss t) = RProp ss (F.subst su t)

  substf f (RProp  ss t) = RProp ss (F.substf f t)

  substa f (RProp  ss t) = RProp ss (F.substa f t)


instance (F.Subable r, IsReft r, TyConable c, F.Binder v, F.Refreshable v, F.Variable r ~ v, ReftBind r ~ v) => F.Subable (RTypeBV v v c tv r) where
  type Variable (RTypeBV v v c tv r) = v
  syms = go
    where
      deletev r0 = case toConcreteReft r0 of
        ConcreteNoReft -> id
        ConcreteReft r -> S.delete (F.reftBind r)
        ConcreteUReft (MkUReft r _) -> S.delete (F.reftBind r)

      go :: RTypeBV v v c tv r -> S.HashSet v
      go (RVar _ r) = F.syms r
      go (RFun x _ t1 t2 r)  =
        -- x scopes over t1, t2, and r
        deletev r (S.delete x $ F.syms t1 `S.union` F.syms t2)
        `S.union` F.syms r
      go (RAllT α t r)       =
        let kindSyms = maybe S.empty (F.syms . snd) (rTVarToBind α)
            deleteα = maybe id (S.delete . fst) (rTVarToBind α)
         in
            deletev r (kindSyms `S.union` deleteα (F.syms t))
            `S.union` F.syms r
      go (RAllP pb t) =
        let (bs, tss) =
              List.mapAccumL
                (\bs0 (tb, b, _) -> (S.insert b bs0, F.syms tb `S.difference` bs0))
                S.empty
                (pargs pb)
         in S.unions $
              S.delete (pname pb) (F.syms t)
              : F.syms (ptype pb) `S.difference` bs
              : tss
      go (RApp _ ts ps r) =
        deletev r (F.syms ts `S.union` F.syms ps)
        `S.union` F.syms r
      go (REx x t1 t2) =
        -- x scopes over t2 only
        F.syms t1 `S.union` S.delete x (F.syms t2)
      go (RExprArg e) = F.syms e
      go (RAppTy t1 t2 r) =
        deletev r (F.syms t1 `S.union` F.syms t2)
        `S.union` F.syms r
      go (RRTy env r _ t) =
          -- env scopes over the refinement type
          let (bs, envSyms) = symsEnv env
              rsyms = F.syms r `S.difference` bs
           in
              envSyms `S.union` rsyms `S.union` F.syms t
        where
          symsEnv = foldl'
              (\(s, env') (x, xt) ->
                let s' = S.insert x s
                 in (s', (F.syms xt `S.difference` s) `S.union` env')
              )
              (S.empty, S.empty)

      go (RHole r) = F.syms r

  -- 'substa' will substitute bound vars
  substa f    = emapExprArg (\_ -> F.substa f) []      . mapReft  (F.substa f)
  -- 'substf' will NOT substitute bound vars
  substf f    = emapExprArg (\_ -> F.substf f) []      . emapReft (F.substf . F.substfExcept f) []
  substr ns su = emapExprArg (\_ -> F.substr ns su) [] . emapReft (\xs -> F.substr ns (F.substExcept su xs)) []
  subst su    = emapExprArg (\_ -> F.subst su) []      . emapReft (F.subst  . F.substExcept su) []
  subst1 t su = emapExprArg (\_ e -> F.subst1 e su) [] $ emapReft (\xs r -> F.subst1Except xs r su) [] t


--------------------------------------------------------------------------------
-- | Visitors ------------------------------------------------------------------
--------------------------------------------------------------------------------
mapExprReft :: (b -> ExprBV b v -> ExprBV b v) -> RTypeBV b v c tv (RReftBV b v) -> RTypeBV b v c tv (RReftBV b v)
mapExprReft f = mapReft g
  where
    g (MkUReft (F.Reft (x, e)) p) = MkUReft (F.Reft (x, f x e)) p

isTrivial :: (IsReft r, IsReft r, TyConable c, F.Binder b, ReftBind r ~ b, Eq (ReftVar r)) => RTypeBV b v c tv r -> Bool
isTrivial = foldReft False (\_ r b -> isTauto r && b) True

mapReft ::  (r1 -> r2) -> RTypeBV b v c tv r1 -> RTypeBV b v c tv r2
mapReft f = emapReft (const f) []

instance Top r => Top (RTypeBV b v c tv r) where
  top (RHole _) = panic Nothing "top called on (RProp _ (RHole _))"
  top t = mapReft top t

emapReft ::  ([b] -> r1 -> r2) -> [b] -> RTypeBV b v c tv r1 -> RTypeBV b v c tv r2
emapReft f γ (RVar α r)        = RVar  α (f γ r)
emapReft f γ (RAllT α t r)     = RAllT α (emapReft f γ t) (f γ r)
emapReft f γ (RAllP π t)       = RAllP π (emapReft f γ t)
emapReft f γ (RFun x i t t' r) = RFun  x i (emapReft f γ t) (emapReft f (x:γ) t') (f (x:γ) r)
emapReft f γ (RApp c ts rs r)  = RApp  c (emapReft f γ <$> ts) (emapRef f γ <$> rs) (f γ r)
emapReft f γ (REx z t t')      = REx   z (emapReft f γ t) (emapReft f γ t')
emapReft _ _ (RExprArg e)      = RExprArg e
emapReft f γ (RAppTy t t' r)   = RAppTy (emapReft f γ t) (emapReft f γ t') (f γ r)
emapReft f γ (RRTy e r o t)    = RRTy  (fmap (emapReft f γ) <$> e) (f γ r) o (emapReft f γ t)
emapReft f γ (RHole r)         = RHole (f γ r)

emapRef :: ([b] -> t -> s) ->  [b] -> RTPropBV b v c tv t -> RTPropBV b v c tv s
emapRef  f γ (RProp s (RHole r))  = RProp s $ RHole (f γ r)
emapRef  f γ (RProp s t)         = RProp s $ emapReft f γ t

mapRTVarV :: (v -> v') -> RTVar b v c tv -> RTVar b v' c tv
mapRTVarV _ (RTVar tv (RTVNoInfo p))         = RTVar tv (RTVNoInfo p)
mapRTVarV f (RTVar tv ri@RTVInfo{rtv_kind=k}) = RTVar tv ri{rtv_kind = coerce (mapRTypeV f k)}

mapRTypeV ::  (v -> v') -> RTypeBV b v c tv r -> RTypeBV b v' c tv r
mapRTypeV _ (RVar α r)        = RVar α r
mapRTypeV f (RAllT α t r)     = RAllT (mapRTVarV f (coerce α)) (mapRTypeV f t) r
mapRTypeV f (RAllP π t)       = RAllP (mapPVarV f (mapRTypeV f) $ coerce π) (mapRTypeV f t)
mapRTypeV f (RFun x i t t' r) = RFun x i (mapRTypeV f t) (mapRTypeV f t') r
mapRTypeV f (RApp c ts rs r)  = RApp c (mapRTypeV f <$> ts) (mapRefV <$> coerce rs) r
  where
    mapRefV (RProp ss t) = RProp (map (fmap (mapRTypeV f)) ss) (mapRTypeV f t)
mapRTypeV f (REx z t t')      = REx z (mapRTypeV f t) (mapRTypeV f t')
mapRTypeV f (RExprArg e)      = RExprArg (fmap (fmap f) e)
mapRTypeV f (RAppTy t t' r)   = RAppTy (mapRTypeV f t) (mapRTypeV f t') r
mapRTypeV f (RRTy e r o t)    = RRTy (fmap (mapRTypeV f) <$> e) r o (mapRTypeV f t)
mapRTypeV _ (RHole r)         = RHole r

mapRTVarVM :: (Hashable b, Monad m) => (v -> m v') -> RTVar b v c tv -> m (RTVar b v' c tv)
mapRTVarVM _ (RTVar tv (RTVNoInfo p))         = pure $ RTVar tv (RTVNoInfo p)
mapRTVarVM f (RTVar tv ri@RTVInfo{rtv_kind=k}) = do
  k' <- mapRTypeVM f k
  pure $ RTVar tv ri{rtv_kind = coerce k'}

mapRTypeVM :: (Hashable b, Monad m) => (v -> m v') -> RTypeBV b v c tv r -> m (RTypeBV b v' c tv r)
mapRTypeVM _ (RVar α r)        = return $ RVar α r
mapRTypeVM f (RAllT α t r)     = RAllT <$> mapRTVarVM f (coerce α) <*> mapRTypeVM f t <*> pure r
mapRTypeVM f (RAllP π t)       = RAllP <$> emapPVarVM (const f) (const (mapRTypeVM f)) (coerce π) <*> mapRTypeVM f t
mapRTypeVM f (RFun x i t t' r) = RFun x i <$> mapRTypeVM f t <*> mapRTypeVM f t' <*> pure r
mapRTypeVM f (RApp c ts rs r)  = RApp c <$> mapM (mapRTypeVM f) ts <*> mapM mapRefVM (coerce rs) <*> pure r
  where
    mapRefVM (RProp ss t) = RProp <$> mapM (traverse (mapRTypeVM f)) ss <*> mapRTypeVM f t
mapRTypeVM f (REx z t t')      = REx z <$> mapRTypeVM f t <*> mapRTypeVM f t'
mapRTypeVM f (RExprArg e)      = RExprArg <$> traverse (traverse f) e
mapRTypeVM f (RAppTy t t' r)   = RAppTy <$> mapRTypeVM f t <*> mapRTypeVM f t' <*> pure r
mapRTypeVM f (RRTy e r o t)    = RRTy <$> mapM (traverse (mapRTypeVM f)) e <*> pure r <*> pure o <*> mapRTypeVM f t
mapRTypeVM _ (RHole r)         = return (RHole r)

emapFReftM :: Monad m => ([Symbol] -> v -> m v') -> F.ReftV v -> m (F.ReftV v')
emapFReftM f (F.Reft (v, e)) = F.reft v <$> emapExprVM (f . (v:)) e

-- The first parameter corresponds to the bscope config setting
emapReftM
  :: forall m b v1 v2 c tv r1 r2. (Monad m, IsReft r1, F.Binder b, CompatibleBinder b tv, ReftBind r1 ~ b)
  => Bool
  -> ([b] -> v1 -> m v2)
  -> ([b] -> r1 -> m r2)
  -> [b]
  -> RTypeBV b v1 c tv r1
  -> m (RTypeBV b v2 c tv r2)
emapReftM bscp vf f = go
  where
    emapRTVarM :: (RTypeBV b v1 c tv (NoReftBV b v1) -> m (RTypeBV b v2 c tv (NoReftBV b v1))) -> RTVar b v1 c tv -> m (RTVar b v2 c tv)
    emapRTVarM _ (RTVar tv (RTVNoInfo p))          = pure $ RTVar tv (RTVNoInfo p)
    emapRTVarM rf (RTVar tv ri@RTVInfo{rtv_kind=k}) = do
      t' <- rf k
      pure $ RTVar tv ri{rtv_kind = coerce t'}

    go :: [b] -> RTypeBV b v1 c tv r1 -> m (RTypeBV b v2 c tv r2)
    go γ (RVar α r)        = RVar  α <$> f γ r
    go γ (RAllT α t r)     = RAllT <$> emapRTVarM (emapReftM bscp vf (const pure) γ) (coerce α) <*> go (coerceBinder (ty_var_value α) : γ) t <*> f γ r
    go γ (RAllP π t)       = RAllP <$> emapPVarVM vf (emapReftM bscp vf (const pure)) (coerce π) <*> go γ t
    go γ (RFun x i t t' r) = RFun  x i <$> go (x:γ) t <*> go (x:γ) t' <*> f (x:γ) r
    go γ (RApp c ts rs r)  =
      let γ' = if bscp then F.reftBind (toReft r) : γ  else γ
       in RApp  c <$> mapM (go γ') ts <*> mapM (emapRefM bscp vf f γ) rs <*> f γ r
    go γ (REx z t t')      = REx   z <$> go γ t <*> go γ t'
    go γ (RExprArg e)      = RExprArg <$> traverse (emapExprVM (vf . (++γ))) e
    go γ (RAppTy t t' r)   = RAppTy <$> go γ t <*> go γ t' <*> f γ r
    go γ (RRTy e r o t)    =
      RRTy <$> mapM (traverse (go (map fst e ++ γ))) e <*> f γ r <*> pure o <*> go γ t
    go γ (RHole r)         = RHole <$> f γ r

emapRefM
  :: (Monad m, IsReft t, F.Binder b, CompatibleBinder b tv, ReftBind t ~ b)
  => Bool
  -> ([b] -> v -> m v')
  -> ([b] -> t -> m s)
  -> [b]
  -> RTPropBV b v c tv t
  -> m (RTPropBV b v' c tv s)
emapRefM bscp vf f γ0 (RProp ss t0) =
    RProp . snd <$>
      mapAccumM
        (\γ (s, t) -> (s:γ,) . (s,) <$> emapReftM bscp vf (const pure) γ t)
        γ0
        (coerce ss)
      <*> emapReftM bscp vf f (map fst ss ++ γ0) t0

emapBareTypeVM
  :: Monad m
  => Bool
  -> ([Symbol] -> v1 -> m v2)
  -> [Symbol]
  -> BareTypeV v1
  -> m (BareTypeV v2)
emapBareTypeVM bscp f =
    emapReftM
      bscp
      f
      (\e -> emapUReftVM (f . (++ e)) (emapFReftM (f . (++ e))))

mapDataDeclV :: (v -> v') -> DataDeclP v ty -> DataDeclP v' ty
mapDataDeclV f DataDecl {..} =
    DataDecl
      { tycPVars = map (mapPVarV f (mapRTypeV f)) (coerce tycPVars)
      , tycSFun = fmap (fmap f) tycSFun
      , ..
      }

mapDataDeclVM :: Monad m => (v -> m v') -> DataDeclP v ty -> m (DataDeclP v' ty)
mapDataDeclVM f = emapDataDeclM False (const f) (const pure)

emapDataDeclM
  :: Monad m
  => Bool
  -> ([Symbol] -> v -> m v')
  -> ([Symbol] -> ty -> m ty')
  -> DataDeclP v ty
  -> m (DataDeclP v' ty')
emapDataDeclM bscp vf f d = do
    tycPVars <- mapM (emapPVarVM vf (emapReftM bscp vf (const pure))) $ tycPVars d
    tycDCons <- traverse (mapM (emapDataCtorTyM f)) (tycDCons d)
    tycSFun <- traverse (traverse (vf [])) (tycSFun d)
    tycPropTy <- traverse (f []) $ tycPropTy d
    return d{tycDCons, tycPVars = coerce tycPVars, tycSFun, tycPropTy}

emapDataCtorTyM
  :: Monad m
  => ([Symbol] -> ty -> m ty')
  -> DataCtorP ty
  -> m (DataCtorP ty')
emapDataCtorTyM f d = do
    dcTheta <- mapM (f []) (dcTheta d)
    dcResult <- traverse (f (map (lhNameToUnqualifiedSymbol . fst) (dcFields d))) $ dcResult d
    dcFields <- snd <$> mapAccumM (\γ  (s, t) -> (lhNameToUnqualifiedSymbol s:γ,) . (s,) <$> f γ t) [] (dcFields d)
    return d{dcTheta, dcFields, dcResult}

emapExprArg :: ([b] -> ExprBV b v -> ExprBV b v) -> [b] -> RTypeBV b v c tv r -> RTypeBV b v c tv r
emapExprArg f = go
  where
    go _ t@RVar{}          = t
    go _ t@RHole{}         = t
    go γ (RAllT α t r)     = RAllT α (go γ t) r
    go γ (RAllP π t)       = RAllP π (go γ t)
    go γ (RFun x i t t' r) = RFun  x i (go γ t) (go (x:γ) t') r
    go γ (RApp c ts rs r)  = RApp  c (go γ <$> ts) (mo γ <$> rs) r
    go γ (REx z t t')      = REx   z (go γ t) (go γ t')
    go γ (RExprArg e)      = RExprArg (f γ <$> e) -- <---- actual substitution
    go γ (RAppTy t t' r)   = RAppTy (go γ t) (go γ t') r
    go γ (RRTy e r o t)    = RRTy  (fmap (go γ) <$> e) r o (go γ t)

    mo _ t@(RProp _ RHole{}) = t
    mo γ (RProp s t)         = RProp s (go γ t)

parsedToBareType :: BareTypeParsed -> BareType
parsedToBareType = mapRTypeV F.val . mapReft (mapUReftV F.val (fmap F.val))

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
isBase (REx _ _ t)      = isBase t
isBase _                = False

hasHoleTy :: RType t t1 t2 -> Bool
hasHoleTy (RVar _ _)        = False
hasHoleTy (RAllT _ t _)     = hasHoleTy t
hasHoleTy (RAllP _ t)       = hasHoleTy t
hasHoleTy (RFun _ _ t t' _) = hasHoleTy t || hasHoleTy t'
hasHoleTy (RApp _ ts _ _)   = any hasHoleTy ts
hasHoleTy (REx _ t t')      = hasHoleTy t || hasHoleTy t'
hasHoleTy (RExprArg _)      = False
hasHoleTy (RAppTy t t' _)   = hasHoleTy t || hasHoleTy t'
hasHoleTy (RHole _)         = True
hasHoleTy (RRTy xts _ _ t)  = hasHoleTy t || any hasHoleTy (snd <$> xts)

isFunTy :: RType t t1 t2 -> Bool
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
mapReftM f (REx z t t')      = liftM2 (REx z)    (mapReftM f t)         (mapReftM f t')
mapReftM _ (RExprArg e)      = return $ RExprArg e
mapReftM f (RAppTy t t' r)   = liftM3 RAppTy (mapReftM f t) (mapReftM f t') (f r)
mapReftM f (RHole r)         = fmap   RHole      (f r)
mapReftM f (RRTy xts r o t)  = liftM4 RRTy (mapM (traverse (mapReftM f)) xts) (f r) (return o) (mapReftM f t)

mapRefM  :: (Monad m) => (t -> m s) -> RTProp c tv t -> m (RTProp c tv s)
mapRefM  f (RProp s t)        = fmap    (RProp s)      (mapReftM f t)

mapPropM :: (Monad m) => (RTProp c tv r -> m (RTProp c tv r)) -> RType c tv r -> m (RType c tv r)
mapPropM _ (RVar α r)        = return $ RVar  α r
mapPropM f (RAllT α t r)     = liftM2 (RAllT α)   (mapPropM f t)          (return r)
mapPropM f (RAllP π t)       = fmap   (RAllP π)   (mapPropM f t)
mapPropM f (RFun x i t t' r) = liftM3 (RFun x i)  (mapPropM f t)          (mapPropM f t') (return r)
mapPropM f (RApp c ts rs r)  = liftM3 (RApp  c)   (mapM (mapPropM f) ts)  (mapM f rs)     (return r)
mapPropM f (REx z t t')      = liftM2 (REx z)     (mapPropM f t)          (mapPropM f t')
mapPropM _ (RExprArg e)      = return $ RExprArg e
mapPropM f (RAppTy t t' r)   = liftM3 RAppTy (mapPropM f t) (mapPropM f t') (return r)
mapPropM _ (RHole r)         = return $ RHole r
mapPropM f (RRTy xts r o t)  = liftM4 RRTy (mapM (traverse (mapPropM f)) xts) (return r) (return o) (mapPropM f t)


--------------------------------------------------------------------------------
foldReft :: (IsReft r, TyConable c, F.Binder b, ReftBind r ~ b) => BScope -> (F.SEnvB b (RTypeBV b v c tv r) -> r -> z -> z) -> z -> RTypeBV b v c tv r -> z
--------------------------------------------------------------------------------
foldReft bsc f = foldReft' bsc id (\γ _ -> f γ)

--------------------------------------------------------------------------------
foldReft' :: (IsReft r, TyConable c, F.Binder b, ReftBind r ~ b)
          => BScope
          -> (RTypeBV b v c tv r -> a)
          -> (F.SEnvB b a -> Maybe (RTypeBV b v c tv r) -> r -> z -> z)
          -> z -> RTypeBV b v c tv r -> z
--------------------------------------------------------------------------------
foldReft' bsc g f
  = efoldReft bsc
              (\_ _ -> [])
              (const [])
              g
              (\γ t r z -> f γ t r z)
              (\_ γ -> γ)
              F.emptySEnv

tyVarIsVal :: RTVar b v c tv -> Bool
tyVarIsVal = rtvinfoIsVal . ty_var_info

rtvinfoIsVal :: RTVInfo b v c tv -> Bool
rtvinfoIsVal RTVNoInfo{} = False
rtvinfoIsVal RTVInfo{..} = rtv_is_val

efoldReft :: (IsReft r, TyConable c, F.Binder b, ReftBind r ~ b)
          => BScope
          -> (c  -> [RTypeBV b v c tv r] -> [(b, a)])
          -> (RTVar b v c tv -> [(b, a)])
          -> (RTypeBV b v c tv r -> a)
          -> (F.SEnvB b a -> Maybe (RTypeBV b v c tv r) -> r -> z -> z)
          -> (PVarBV b v (RTypeBV b v c tv (NoReftBV b v)) -> F.SEnvB b a -> F.SEnvB b a)
          -> F.SEnvB b a
          -> z
          -> RTypeBV b v c tv r
          -> z
efoldReft bsc cb dty g f fp = go
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
    go γ z me@(RFun x _ t t' r)         = f γ (Just me) r (go γ' (go γ z t) t')
       where
         γ'                             = insertSEnv x (g t) γ
    go γ z me@(RApp _ ts rs r)          = f γ (Just me) r (ho' γ (go' γ' z ts) rs)
       where γ' = if bsc then insertSEnv (rTypeValueVar me) (g me) γ else γ

    go γ z (REx x t t')                 = go (insertSEnv x (g t) γ) (go γ z t) t'
    go γ z me@(RRTy [] r _ t)           = f γ (Just me) r (go γ z t)
    go γ z me@(RRTy xts r _ t)          = f γ (Just me) r (go γ (go γ z (envtoType xts)) t)
    go γ z me@(RAppTy t t' r)           = f γ (Just me) r (go γ (go γ z t) t')
    go _ z (RExprArg _)                 = z
    go γ z me@(RHole r)                 = f γ (Just me) r z

    -- folding over Ref
    ho  γ z (RProp ss (RHole r))       = f (insertsSEnv γ (fmap (g . ofRSort) <$> ss)) Nothing r z
    ho  γ z (RProp ss t)               = go (insertsSEnv γ (fmap (g . ofRSort) <$> ss)) z t

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
mapRFInfo f (RRTy e r o t)    = RRTy (fmap (mapRFInfo f) <$> e) r o (mapRFInfo f t)
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
mapBot f (RRTy e r o t)    = RRTy (fmap (mapBot f) <$> e) r o (mapBot f t)
mapBot f t'                = f t'

mapBotRef :: (RType c tv r -> RType c tv r)
          -> Ref τ (RType c tv r) -> Ref τ (RType c tv r)
mapBotRef _ (RProp s (RHole r)) = RProp s $ RHole r
mapBotRef f (RProp s t)         = RProp s $ mapBot f t

mapBind :: (Hashable b, Hashable b') => (b -> b') -> RTypeBV b v c tv r -> RTypeBV b' v c tv r
mapBind f = go
  where
    go (RAllT α t r)      = RAllT (mapT α) (go t) r
    go (RAllP π t)        = RAllP (mapP π) (go t)
    go (RFun b i t1 t2 r) = RFun (f b) i (go t1) (go t2) r
    go (RApp c ts rs r)   = RApp c (go <$> ts) (mapR <$> rs) r
    go (REx b t1 t2)      = REx    (f b) (go t1) (go t2)
    go (RVar α r)         = RVar α r
    go (RHole r)          = RHole r
    go (RRTy e r o t)     = RRTy (bimap f go <$> e) r o (go t)
    go (RExprArg e)       = RExprArg (F.mapBindExpr f <$> e)
    go (RAppTy t t' r)    = RAppTy (go t) (go t') r
    mapT (RTVar tv i)     = RTVar tv (mapI i)
    mapS                  = mapReft (\NoReft -> NoReft) . mapBind f
    mapI RTVNoInfo{..}    = RTVNoInfo{..}
    mapI RTVInfo{..}      = RTVInfo {rtv_name = f rtv_name, rtv_kind = mapS rtv_kind, .. }
    mapP (PV n τ as)    = PV (f n) (mapS τ) (mapA <$> as)
    mapA (τ, b, e)        = (mapS τ, f b, F.mapBindExpr f e)
    mapR (RProp as t)     = RProp (bimap f mapS <$> as) (go t)

--------------------------------------------------
ofRSort ::  IsReft r => RTypeBV b v c tv (NoReftBV b v) -> RTypeBV b v c tv r
ofRSort = fmap (const trueReft)

toRSort :: F.Binder b => RTypeBV b v c tv r -> RTypeBV b v c tv (NoReftBV b v)
toRSort = stripAnnotations . mapBind (const F.wildcard) . (NoReft <$)

stripAnnotations :: RTypeBV b v c tv r -> RTypeBV b v c tv r
stripAnnotations (RAllT α t r)     = RAllT α (stripAnnotations t) r
stripAnnotations (RAllP _ t)       = stripAnnotations t
stripAnnotations (REx _ _ t)       = stripAnnotations t
stripAnnotations (RFun x i t t' r) = RFun x i (stripAnnotations t) (stripAnnotations t') r
stripAnnotations (RAppTy t t' r)   = RAppTy (stripAnnotations t) (stripAnnotations t') r
stripAnnotations (RApp c ts rs r)  = RApp c (stripAnnotations <$> ts) (stripAnnotationsRef <$> rs) r
stripAnnotations (RRTy _ _ _ t)    = stripAnnotations t
stripAnnotations t                 = t

stripAnnotationsRef :: RefB b τ (RTypeBV b v c tv r) -> RefB b τ (RTypeBV b v c tv r)
stripAnnotationsRef (RProp s (RHole r)) = RProp s (RHole r)
stripAnnotationsRef (RProp s t)         = RProp s $ stripAnnotations t

insertSEnv :: (Eq b, Hashable b) => b -> a -> F.SEnvB b a -> F.SEnvB b a
insertSEnv = F.insertSEnv

insertsSEnv :: (Eq b, Hashable b) => F.SEnvB b a -> [(b, a)] -> F.SEnvB b a
insertsSEnv  = foldr (\(x, t) γ -> insertSEnv x t γ)

rTypeValueVar :: (IsReft r, F.Binder (ReftBind r)) => RTypeBV b v c tv r -> ReftBind r
rTypeValueVar t = vv where F.Reft (vv,_) =  rTypeReft t

rTypeReft :: (IsReft r, F.Binder (ReftBind r)) => RTypeBV b v c tv r -> F.ReftBV (ReftBind r) (ReftVar r)
rTypeReft = maybe F.trueReft toReft . stripRTypeBase

-- stripRTypeBase ::  RType a -> Maybe a
stripRTypeBase :: RTypeBV b v c tv r -> Maybe r
stripRTypeBase (RApp _ _ _ x)   = Just x
stripRTypeBase (RVar _ x)       = Just x
stripRTypeBase (RFun _ _ _ _ x) = Just x
stripRTypeBase (RAppTy _ _ x)   = Just x
stripRTypeBase (RAllT _ _ x)    = Just x
stripRTypeBase _                = Nothing

topRTypeBase :: (Top r) => RType c tv r -> RType c tv r
topRTypeBase = mapRBase top

mapRBase :: (r -> r) -> RType c tv r -> RType c tv r
mapRBase f (RApp c ts rs r)   = RApp c ts rs $ f r
mapRBase f (RVar a r)         = RVar a $ f r
mapRBase f (RFun x i t1 t2 r) = RFun x i t1 t2 $ f r
mapRBase f (RAppTy t1 t2 r)   = RAppTy t1 t2 $ f r
mapRBase f (RAllT b t r)      = RAllT b t (f r)
mapRBase _ t                  = t
