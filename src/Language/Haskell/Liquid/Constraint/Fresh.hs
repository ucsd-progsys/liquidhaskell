{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE BangPatterns          #-}

module Language.Haskell.Liquid.Constraint.Fresh
  ( Freshable(..)
  , refreshTy
  , refreshVV
  , refreshArgs
  , refreshArgsTop
  , refreshHoles
  , freshTy_type
  , freshTy_expr
  , trueTy
  , addKuts  
  )
  where

import           Data.Maybe                    (catMaybes) -- , fromJust, isJust)
import           Data.Bifunctor
import qualified Data.List                      as L
import qualified Data.HashMap.Strict            as M
import qualified Data.HashSet                   as S
import           Data.Hashable
import           Control.Monad.State            (get, put, modify)
import           Control.Monad                  (when, (>=>))
import           Prelude                        hiding (error)

import           CoreUtils  (exprType)
import           Type       (Type)
import           CoreSyn
import           Var        (varType, isTyVar, Var)

import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Types.Visitor (kvars)
import           Language.Haskell.Liquid.Misc  (single, (=>>))
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Constraint.Types

class (Applicative m, Monad m) => Freshable m a where
  fresh   :: m a
  true    :: a -> m a
  true    = return
  refresh :: a -> m a
  refresh = return

instance Freshable CG Integer where
  fresh = do s <- get
             let n = freshIndex s
             put $ s { freshIndex = n + 1 }
             return n

instance Freshable m Integer => Freshable m F.Symbol where
  fresh = F.tempSymbol "x" <$> fresh

instance Freshable m Integer => Freshable m F.Expr where
  fresh  = kv <$> fresh
    where
      kv = (`F.PKVar` mempty) . F.intKvar

instance Freshable m Integer => Freshable m [F.Expr] where
  fresh = single <$> fresh

instance Freshable m Integer => Freshable m F.Reft where
  fresh                  = panic Nothing "fresh Reft"
  true    (F.Reft (v,_)) = return $ F.Reft (v, mempty)
  refresh (F.Reft (_,_)) = (F.Reft .) . (,) <$> freshVV <*> fresh
    where
      freshVV            = F.vv . Just <$> fresh

instance Freshable m Integer => Freshable m RReft where
  fresh             = panic Nothing "fresh RReft"
  true (MkUReft r _ s)    = MkUReft <$> true r    <*> return mempty <*> true s
  refresh (MkUReft r _ s) = MkUReft <$> refresh r <*> return mempty <*> refresh s

instance Freshable m Integer => Freshable m Strata where
  fresh      = (:[]) . SVar <$> fresh
  true []    = fresh
  true s     = return s
  refresh [] = fresh
  refresh s  = return s

instance (Freshable m Integer, Freshable m r, F.Reftable r ) => Freshable m (RRType r) where
  fresh   = panic Nothing "fresh RefType"
  refresh = refreshRefType
  true    = trueRefType

-----------------------------------------------------------------------------------------------
trueRefType :: (Freshable m Integer, Freshable m r, F.Reftable r) => RRType r -> m (RRType r)
-----------------------------------------------------------------------------------------------
trueRefType (RAllT α t)
  = RAllT α <$> true t

trueRefType (RAllP π t)
  = RAllP π <$> true t

trueRefType (RFun _ t t' _)
  = rFun <$> fresh <*> true t <*> true t'

trueRefType (RApp c ts _  _) | isClass c
  = rRCls c <$> mapM true ts

trueRefType (RApp c ts rs r)
  = RApp c <$> mapM true ts <*> mapM trueRef rs <*> true r

trueRefType (RAppTy t t' _)
  = RAppTy <$> true t <*> true t' <*> return mempty

trueRefType (RVar a r)
  = RVar a <$> true r

trueRefType (RAllE y ty tx)
  = do y'  <- fresh
       ty' <- true ty
       tx' <- true tx
       return $ RAllE y' ty' (tx' `F.subst1` (y, F.EVar y'))

trueRefType (RRTy e o r t)
  = RRTy e o r <$> trueRefType t

trueRefType t
  = return t

trueRef :: (F.Reftable r, Freshable f r, Freshable f Integer)
        => Ref τ (RType RTyCon RTyVar r) -> f (Ref τ (RRType r))
trueRef (RProp _ (RHole _)) = panic Nothing "trueRef: unexpected RProp _ (RHole _))"
trueRef (RProp s t) = RProp s <$> trueRefType t


-----------------------------------------------------------------------------------------------
refreshRefType :: (Freshable m Integer, Freshable m r, F.Reftable r) => RRType r -> m (RRType r)
-----------------------------------------------------------------------------------------------
refreshRefType (RAllT α t)
  = RAllT α <$> refresh t

refreshRefType (RAllP π t)
  = RAllP π <$> refresh t

refreshRefType (RFun b t t' _)
  | b == F.dummySymbol = rFun <$> fresh <*> refresh t <*> refresh t'
  | otherwise          = rFun     b     <$> refresh t <*> refresh t'

refreshRefType (RApp rc ts _ _) | isClass rc
  = return $ rRCls rc ts

refreshRefType (RApp rc ts rs r)
  = RApp rc <$> mapM refresh ts <*> mapM refreshRef rs <*> refresh r

refreshRefType (RVar a r)
  = RVar a <$> refresh r

refreshRefType (RAppTy t t' r)
  = RAppTy <$> refresh t <*> refresh t' <*> refresh r

refreshRefType (RAllE y ty tx)
  = do y'  <- fresh
       ty' <- refresh ty
       tx' <- refresh tx
       return $ RAllE y' ty' (tx' `F.subst1` (y, F.EVar y'))

refreshRefType (RRTy e o r t)
  = RRTy e o r <$> refreshRefType t

refreshRefType t
  = return t

refreshRef :: (F.Reftable r, Freshable f r, Freshable f Integer)
           => Ref τ (RType RTyCon RTyVar r) -> f (Ref τ (RRType r))
refreshRef (RProp _ (RHole _)) = panic Nothing "refreshRef: unexpected (RProp _ (RHole _))"
refreshRef (RProp s t) = RProp <$> mapM freshSym s <*> refreshRefType t

freshSym :: Freshable f a => (t, t1) -> f (a, t1)
freshSym (_, t)        = (, t) <$> fresh


--------------------------------------------------------------------------------
refreshTy :: SpecType -> CG SpecType
--------------------------------------------------------------------------------
refreshTy t = refreshVV t >>= refreshArgs

refreshVV :: Freshable m Integer => SpecType -> m SpecType
refreshVV (RAllT a t) = RAllT a <$> refreshVV t
refreshVV (RAllP p t) = RAllP p <$> refreshVV t

refreshVV (REx x t1 t2)
  = do [t1', t2'] <- mapM refreshVV [t1, t2]
       shiftVV (REx x t1' t2') <$> fresh

refreshVV (RFun x t1 t2 r)
  = do [t1', t2'] <- mapM refreshVV [t1, t2]
       shiftVV (RFun x t1' t2' r) <$> fresh

refreshVV (RAppTy t1 t2 r)
  = do [t1', t2'] <- mapM refreshVV [t1, t2]
       shiftVV (RAppTy t1' t2' r) <$> fresh

refreshVV (RApp c ts rs r)
  = do ts' <- mapM refreshVV ts
       rs' <- mapM refreshVVRef rs
       shiftVV (RApp c ts' rs' r) <$> fresh

refreshVV t
  = return t

refreshVVRef :: Freshable m Integer
             => Ref b (RType RTyCon RTyVar RReft)
             -> m (Ref b (RType RTyCon RTyVar RReft))
refreshVVRef (RProp ss (RHole r))
  = return $ RProp ss (RHole r)

refreshVVRef (RProp ss t)
  = do xs    <- mapM (const fresh) (fst <$> ss)
       let su = F.mkSubst $ zip (fst <$> ss) (F.EVar <$> xs)
       (RProp (zip xs (snd <$> ss)) . F.subst su) <$> refreshVV t

--------------------------------------------------------------------------------
refreshArgsTop :: (Var, SpecType) -> CG SpecType
--------------------------------------------------------------------------------
refreshArgsTop (x, t)
  = do (t', su) <- refreshArgsSub t
       modify $ \s -> s {termExprs = M.adjust (F.subst su <$>) x $ termExprs s}
       return t'

--------------------------------------------------------------------------------
refreshArgs :: SpecType -> CG SpecType
--------------------------------------------------------------------------------
refreshArgs t = fst <$> refreshArgsSub t


-- NV TODO: this does not refresh args if they are wrapped in an RRTy
refreshArgsSub :: SpecType -> CG (SpecType, F.Subst)
refreshArgsSub t
  = do ts     <- mapM refreshArgs ts_u
       xs'    <- mapM (const fresh) xs
       let sus = F.mkSubst <$> L.inits (zip xs (F.EVar <$> xs'))
       let su  = last sus
       ts'    <- mapM refreshPs $ zipWith F.subst sus ts
       let rs' = zipWith F.subst sus rs
       tr     <- refreshPs $ F.subst su tbd
       let t'  = fromRTypeRep $ trep {ty_binds = xs', ty_args = ts', ty_res = tr, ty_refts = rs'}
       return (t', su)
    where
       trep    = toRTypeRep t
       xs      = ty_binds trep
       ts_u    = ty_args  trep
       tbd     = ty_res   trep
       rs      = ty_refts trep

refreshPs :: SpecType -> CG SpecType
refreshPs = mapPropM go
  where
    go (RProp s t) = do
      t'    <- refreshPs t
      xs    <- mapM (const fresh) s
      let su = F.mkSubst [(y, F.EVar x) | (x, (y, _)) <- zip xs s]
      return $ RProp [(x, t) | (x, (_, t)) <- zip xs s] $ F.subst su t'

--------------------------------------------------------------------------------
refreshHoles :: (F.Symbolic t, F.Reftable r, TyConable c, Freshable f r)
             => [(t, RType c tv r)] -> f ([F.Symbol], [(t, RType c tv r)])
refreshHoles vts = first catMaybes . unzip . map extract <$> mapM refreshHoles' vts
  where
  --   extract :: (t, t1, t2) -> (t, (t1, t2))
    extract (a,b,c) = (a,(b,c))

refreshHoles' :: (F.Symbolic a, F.Reftable r, TyConable c, Freshable m r)
              => (a, RType c tv r) -> m (Maybe F.Symbol, a, RType c tv r)
refreshHoles' (x,t)
  | noHoles t = return (Nothing, x, t)
  | otherwise = (Just $ F.symbol x,x,) <$> mapReftM tx t
  where
    tx r | hasHole r = refresh r
         | otherwise = return r

noHoles :: (F.Reftable r, TyConable c) => RType c tv r -> Bool
noHoles = and . foldReft (\_ r bs -> not (hasHole r) : bs) []

--------------------------------------------------------------------------------
-- | Generation: Freshness -----------------------------------------------------
--------------------------------------------------------------------------------

-- | Right now, we generate NO new pvars. Rather than clutter code
--   with `uRType` calls, put it in one place where the above
--   invariant is /obviously/ enforced.
--   Constraint generation should ONLY use @freshTy_type@ and @freshTy_expr@

freshTy_type        :: KVKind -> CoreExpr -> Type -> CG SpecType
freshTy_type k _ τ  = freshTy_reftype k $ ofType τ

freshTy_expr        :: KVKind -> CoreExpr -> Type -> CG SpecType
freshTy_expr k e _  = freshTy_reftype k $ exprRefType e

freshTy_reftype     :: KVKind -> SpecType -> CG SpecType
freshTy_reftype k _t = (fixTy t >>= refresh) =>> addKVars k
  where
    t                = {- F.tracepp ("freshTy_reftype:" ++ show k) -} _t

-- | Used to generate "cut" kvars for fixpoint. Typically, KVars for recursive
--   definitions, and also to update the KVar profile.
addKVars        :: KVKind -> SpecType -> CG ()
addKVars !k !t  = do when (True)    $ modify $ \s -> s { kvProf = updKVProf k ks (kvProf s) }
                     when (isKut k) $ addKuts k t
                     -- when (True)    $ addKvPack t
  where
     ks         = F.KS $ S.fromList $ specTypeKVars t

isKut              :: KVKind -> Bool
isKut (RecBindE _) = True
isKut ProjectE     = True
isKut _            = False

addKuts :: (PPrint a) => a -> SpecType -> CG ()
addKuts _x t = modify $ \s -> s { kuts = mappend (F.KS ks) (kuts s)   }
  where
     ks'     = S.fromList $ specTypeKVars t
     ks
       | S.null ks' = ks'
       | otherwise  = {- F.tracepp ("addKuts: " ++ showpp _x) -} ks'

-- addKvPack :: SpecType -> CG ()
-- addKvPack t = modify $ \s -> s { kvPacks = ks : kvPacks s}
  -- where
    -- ks      = S.fromList $ specTypeKVars t

specTypeKVars :: SpecType -> [F.KVar]
specTypeKVars = foldReft (\ _ r ks -> (kvars $ ur_reft r) ++ ks) []

--------------------------------------------------------------------------------
trueTy  :: Type -> CG SpecType
--------------------------------------------------------------------------------
trueTy = ofType' >=> true

ofType' :: Type -> CG SpecType
ofType' = fixTy . ofType

fixTy :: SpecType -> CG SpecType
fixTy t = do tyi   <- tyConInfo  <$> get
             tce   <- tyConEmbed <$> get
             return $ addTyConInfo tce tyi t

exprRefType :: CoreExpr -> SpecType
exprRefType = exprRefType_ M.empty

exprRefType_ :: M.HashMap Var SpecType -> CoreExpr -> SpecType
exprRefType_ γ (Let b e)
  = exprRefType_ (bindRefType_ γ b) e

exprRefType_ γ (Lam α e) | isTyVar α
  = RAllT (makeRTVar $ rTyVar α) (exprRefType_ γ e)

exprRefType_ γ (Lam x e)
  = rFun (F.symbol x) (ofType $ varType x) (exprRefType_ γ e)

exprRefType_ γ (Tick _ e)
  = exprRefType_ γ e

exprRefType_ γ (Var x)
  = M.lookupDefault (ofType $ varType x) x γ

exprRefType_ _ e
  = ofType $ exprType e

bindRefType_ :: M.HashMap Var SpecType -> Bind Var -> M.HashMap Var SpecType
bindRefType_ γ (Rec xes)
  = extendγ γ [(x, exprRefType_ γ e) | (x,e) <- xes]

bindRefType_ γ (NonRec x e)
  = extendγ γ [(x, exprRefType_ γ e)]

extendγ :: (Eq k, Foldable t, Hashable k)
        => M.HashMap k v
        -> t (k, v)
        -> M.HashMap k v
extendγ γ xts
  = foldr (\(x,t) m -> M.insert x t m) γ xts
