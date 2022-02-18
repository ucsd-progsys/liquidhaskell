{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ConstraintKinds       #-}

module Language.Haskell.Liquid.Types.Fresh
  ( Freshable(..)
  , refreshTy
  , refreshVV
  , refreshArgs
  , refreshHoles
  , refreshArgsSub
  )
  where

import           Data.Maybe                    (catMaybes) -- , fromJust, isJust)
import           Data.Bifunctor
import qualified Data.List                      as L
-- import qualified Data.HashMap.Strict            as M
-- import qualified Data.HashSet                   as S
-- import           Data.Hashable
-- import           Control.Monad.State            (gets, get, put, modify)
-- import           Control.Monad                  (when, (>=>))
-- import           CoreUtils  (exprType)
import           Prelude                        hiding (error)
-- import           Type       (Type)
-- import           CoreSyn
-- import           Var        (varType, isTyVar, Var)

import qualified Language.Fixpoint.Types as F
-- import           Language.Fixpoint.Types.Visitor (kvars)
import           Language.Haskell.Liquid.Misc  (single)
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.RefType


class (Applicative m, Monad m) => Freshable m a where
  fresh   :: m a
  true    :: Bool -> a -> m a
  true _  = return
  refresh :: Bool -> a -> m a
  refresh _ = return


instance (Freshable m Integer, Monad m, Applicative m) => Freshable m F.Symbol where
  fresh = F.tempSymbol "x" <$> fresh

instance (Freshable m Integer, Monad m, Applicative m) => Freshable m F.Expr where
  fresh  = kv <$> fresh
    where
      kv = (`F.PKVar` mempty) . F.intKvar

instance (Freshable m Integer, Monad m, Applicative m) => Freshable m [F.Expr] where
  fresh = single <$> fresh

instance (Freshable m Integer, Monad m, Applicative m) => Freshable m F.Reft where
  fresh                  = panic Nothing "fresh Reft"
  true    _ (F.Reft (v,_)) = return $ F.Reft (v, mempty)
  refresh _ (F.Reft (_,_)) = (F.Reft .) . (,) <$> freshVV <*> fresh
    where
      freshVV            = F.vv . Just <$> fresh

instance Freshable m Integer => Freshable m RReft where
  fresh             = panic Nothing "fresh RReft"
  true allowTC (MkUReft r _)    = MkUReft <$> true allowTC r    <*> return mempty
  refresh allowTC (MkUReft r _) = MkUReft <$> refresh allowTC r <*> return mempty

instance (Freshable m Integer, Freshable m r, F.Reftable r ) => Freshable m (RRType r) where
  fresh   = panic Nothing "fresh RefType"
  refresh = refreshRefType
  true    = trueRefType

-----------------------------------------------------------------------------------------------
trueRefType :: (Freshable m Integer, Freshable m r, F.Reftable r) => Bool -> RRType r -> m (RRType r)
-----------------------------------------------------------------------------------------------
trueRefType allowTC (RAllT α t r)
  = RAllT α <$> true allowTC t <*> true allowTC r 

trueRefType allowTC (RAllP π t)
  = RAllP π <$> true allowTC t

trueRefType allowTC (RImpF _ _ t t' _)
  = rImpF <$> fresh <*> true allowTC t <*> true allowTC t'

trueRefType allowTC (RFun _ _ t t' _)
  -- YL: attaching rfinfo here is crucial
  = rFun' (classRFInfo allowTC) <$> fresh <*> true allowTC t <*> true allowTC t'

trueRefType allowTC (RApp c ts _  _) | if allowTC then isEmbeddedDict c else isClass c
  = rRCls c <$> mapM (true allowTC) ts

trueRefType allowTC (RApp c ts rs r)
  = RApp c <$> mapM (true allowTC) ts <*> mapM (trueRef allowTC) rs <*> true allowTC r

trueRefType allowTC (RAppTy t t' _)
  = RAppTy <$> true allowTC t <*> true allowTC t' <*> return mempty

trueRefType allowTC (RVar a r)
  = RVar a <$> true allowTC r

trueRefType allowTC (RAllE y ty tx)
  = do y'  <- fresh
       ty' <- true allowTC ty
       tx' <- true allowTC tx
       return $ RAllE y' ty' (tx' `F.subst1` (y, F.EVar y'))

trueRefType allowTC (RRTy e o r t)
  = RRTy e o r <$> trueRefType allowTC t

trueRefType allowTC (REx _ t t')
  = REx <$> fresh <*> true allowTC t <*> true allowTC t'

trueRefType _ t@(RExprArg _)
  = return t

trueRefType _ t@(RHole _)
  = return t

trueRef :: (F.Reftable r, Freshable f r, Freshable f Integer)
        => Bool -> Ref τ (RType RTyCon RTyVar r) -> f (Ref τ (RRType r))
trueRef _ (RProp _ (RHole _)) = panic Nothing "trueRef: unexpected RProp _ (RHole _))"
trueRef allowTC (RProp s t) = RProp s <$> trueRefType allowTC t


-----------------------------------------------------------------------------------------------
refreshRefType :: (Freshable m Integer, Freshable m r, F.Reftable r) => Bool -> RRType r -> m (RRType r)
-----------------------------------------------------------------------------------------------
refreshRefType allowTC (RAllT α t r)
  = RAllT α <$> refresh allowTC t <*> true allowTC r

refreshRefType allowTC (RAllP π t)
  = RAllP π <$> refresh allowTC t

refreshRefType allowTC (RImpF b i t t' _)
  | b == F.dummySymbol = (\b t1 t2 -> RImpF b i t1 t2 mempty) <$> fresh <*> refresh allowTC t <*> refresh allowTC t'
  | otherwise          = (\t1 t2 -> RImpF b i t1 t2 mempty)   <$> refresh allowTC t <*> refresh allowTC t'

refreshRefType allowTC (RFun b i t t' _)
  | b == F.dummySymbol = (\b t1 t2 -> RFun b i t1 t2 mempty) <$> fresh <*> refresh allowTC t <*> refresh allowTC t'
  | otherwise          = (\t1 t2 -> RFun b i t1 t2 mempty)   <$> refresh allowTC t <*> refresh allowTC t'

refreshRefType _ (RApp rc ts _ _) | isClass rc
  = return $ rRCls rc ts

refreshRefType allowTC (RApp rc ts rs r)
  = RApp rc <$> mapM (refresh allowTC) ts <*> mapM (refreshRef allowTC) rs <*> refresh allowTC r

refreshRefType allowTC (RVar a r)
  = RVar a <$> refresh allowTC r

refreshRefType allowTC (RAppTy t t' r)
  = RAppTy <$> refresh allowTC t <*> refresh allowTC t' <*> refresh allowTC r

refreshRefType allowTC (RAllE y ty tx)
  = do y'  <- fresh
       ty' <- refresh allowTC ty
       tx' <- refresh allowTC tx
       return $ RAllE y' ty' (tx' `F.subst1` (y, F.EVar y'))

refreshRefType allowTC (RRTy e o r t)
  = RRTy e o r <$> refreshRefType allowTC t

refreshRefType _ t
  = return t

refreshRef :: (F.Reftable r, Freshable f r, Freshable f Integer)
           => Bool -> Ref τ (RType RTyCon RTyVar r) -> f (Ref τ (RRType r))
refreshRef _ (RProp _ (RHole _)) = panic Nothing "refreshRef: unexpected (RProp _ (RHole _))"
refreshRef allowTC (RProp s t) = RProp <$> mapM freshSym s <*> refreshRefType allowTC t

freshSym :: Freshable f a => (t, t1) -> f (a, t1)
freshSym (_, t)        = (, t) <$> fresh


--------------------------------------------------------------------------------
refreshTy :: (FreshM m) => SpecType -> m SpecType
--------------------------------------------------------------------------------
refreshTy t = refreshVV t >>= refreshArgs

--------------------------------------------------------------------------------
type FreshM m = Freshable m Integer
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
refreshVV :: FreshM m => SpecType -> m SpecType
--------------------------------------------------------------------------------
refreshVV (RAllT a t r) = 
  RAllT a <$> refreshVV t <*> return r 

refreshVV (RAllP p t) = 
  RAllP p <$> refreshVV t

refreshVV (REx x t1 t2) = do 
  t1' <- refreshVV t1
  t2' <- refreshVV t2
  shiftVV (REx x t1' t2') <$> fresh

refreshVV (RImpF x i t1 t2 r) = do
  t1' <- refreshVV t1
  t2' <- refreshVV t2
  shiftVV (RImpF x i t1' t2' r) <$> fresh

refreshVV (RFun x i t1 t2 r) = do
  t1' <- refreshVV t1
  t2' <- refreshVV t2
  shiftVV (RFun x i t1' t2' r) <$> fresh

refreshVV (RAppTy t1 t2 r) = do 
  t1' <- refreshVV t1
  t2' <- refreshVV t2
  shiftVV (RAppTy t1' t2' r) <$> fresh

refreshVV (RApp c ts rs r) = do 
  ts' <- mapM refreshVV    ts
  rs' <- mapM refreshVVRef rs
  shiftVV (RApp c ts' rs' r) <$> fresh

refreshVV t = 
  shiftVV t <$> fresh

refreshVVRef :: Freshable m Integer => Ref b SpecType -> m (Ref b SpecType)
refreshVVRef (RProp ss (RHole r))
  = return $ RProp ss (RHole r)

refreshVVRef (RProp ss t)
  = do xs    <- mapM (const fresh) (fst <$> ss)
       let su = F.mkSubst $ zip (fst <$> ss) (F.EVar <$> xs)
       (RProp (zip xs (snd <$> ss)) . F.subst su) <$> refreshVV t

--------------------------------------------------------------------------------
refreshArgs :: (FreshM m) => SpecType -> m SpecType
--------------------------------------------------------------------------------
refreshArgs t = fst <$> refreshArgsSub t


-- NV TODO: this does not refresh args if they are wrapped in an RRTy
refreshArgsSub :: (FreshM m) => SpecType -> m (SpecType, F.Subst)
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

refreshPs :: (FreshM m) => SpecType -> m SpecType
refreshPs = mapPropM go
  where
    go (RProp s t) = do
      t'    <- refreshPs t
      xs    <- mapM (const fresh) s
      let su = F.mkSubst [(y, F.EVar x) | (x, (y, _)) <- zip xs s]
      return $ RProp [(x, t) | (x, (_, t)) <- zip xs s] $ F.subst su t'

--------------------------------------------------------------------------------
refreshHoles :: (F.Symbolic t, F.Reftable r, TyConable c, Freshable f r)
             => Bool -> [(t, RType c tv r)] -> f ([F.Symbol], [(t, RType c tv r)])
refreshHoles allowTC vts = first catMaybes . unzip . map extract <$> mapM (refreshHoles' allowTC) vts
  where
  --   extract :: (t, t1, t2) -> (t, (t1, t2))
    extract (a,b,c) = (a,(b,c))

refreshHoles' :: (F.Symbolic a, F.Reftable r, TyConable c, Freshable m r)
              => Bool -> (a, RType c tv r) -> m (Maybe F.Symbol, a, RType c tv r)
refreshHoles' allowTC (x,t)
  | noHoles t = return (Nothing, x, t)
  | otherwise = (Just $ F.symbol x,x,) <$> mapReftM tx t
  where
    tx r | hasHole r = refresh allowTC r
         | otherwise = return r

noHoles :: (F.Reftable r, TyConable c) => RType c tv r -> Bool
noHoles = and . foldReft False (\_ r bs -> not (hasHole r) : bs) []
