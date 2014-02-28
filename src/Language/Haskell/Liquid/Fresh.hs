{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Language.Haskell.Liquid.Fresh (
  Freshable(..), TCInfo(..)
  ) where

import Control.Monad.State
import Control.Applicative              ((<$>))

import qualified TyCon as TC

import qualified Data.HashMap.Strict as M

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.RefType  (uTop, expandRApp)
import Language.Fixpoint.Types
import Language.Fixpoint.Misc


import Data.Monoid                      (mempty)

type TTCInfo  = M.HashMap TC.TyCon RTyCon
type TTCEmbed = TCEmb TC.TyCon

class Monad m => Freshable m a where
  fresh   :: m a
  true    :: a -> m a
  true    = return . id
  refresh :: a -> m a
  refresh = return . id

class Monad m => TCInfo m where
  getTyConInfo  :: m TTCInfo
  getTyConInfo  = return $ M.empty
  getTyConEmbed :: m TTCEmbed
  getTyConEmbed = return $ M.empty

instance Freshable m Integer => Freshable m Symbol where
  fresh = liftM (tempSymbol "x") fresh

instance Freshable m Integer => Freshable m Refa where
  fresh = liftM (`RKvar` mkSubst []) freshK
    where freshK = liftM intKvar fresh

instance Freshable m Integer => Freshable m [Refa] where
  fresh = liftM single fresh

-- instance Monad m => Freshable m TCEmbed where

instance Freshable m Integer => Freshable m Reft where
  fresh                = errorstar "fresh Reft"
  true    (Reft (v,_)) = return $ Reft (v, [])
  refresh (Reft (_,_)) = liftM2 (curry Reft) freshVV fresh
    where freshVV      = liftM (vv . Just) fresh

instance Freshable m Integer => Freshable m RReft where
  fresh             = errorstar "fresh RReft"
  true (U r _)      = liftM uTop (true r)
  refresh (U r _)   = liftM uTop (refresh r)

instance (Freshable m Integer, Freshable m r, TCInfo m, Reftable r) => Freshable m (RRType r) where
  fresh   = errorstar "fresh RefType"
  refresh = refreshRefType
  true    = trueRefType

trueRefType :: (Freshable m Integer, Freshable m r,TCInfo m,  Reftable r) => RRType r -> m (RRType r)
trueRefType (RAllT α t)
  = liftM (RAllT α) (true t)
trueRefType (RAllP π t)
  = liftM (RAllP π) (true t)
trueRefType (RFun _ t t' _)
  = liftM3 rFun fresh (true t) (true t')
trueRefType (RApp rc ts _ r)
  = do tyi                 <- getTyConInfo
       tce                 <- getTyConEmbed
       let RApp rc' _ rs _  = expandRApp tce tyi (RApp rc ts [] r)
       let rπs              = safeZip "trueRefType" rs (rTyConPs rc')
       liftM3 (RApp rc') (mapM trueRefType ts) (mapM trueRef rπs) (true r)
  -- = liftM (\ts -> RApp c ts truerefs mempty) (mapM true ts)
  --            where truerefs = traceShow "truerefs" $ (RPoly []  . ofRSort . ptype) <$> (rTyConPs c)
trueRefType (RAppTy t t' _)
  = liftM3 RAppTy (true t) (true t') (return mempty)
trueRefType t
  = return t

trueRef rπ = refreshRef 0 rπ


refreshRefType :: (Freshable m Integer, Freshable m r, TCInfo m, Reftable r)
               => RRType r
               -> m (RRType r)
refreshRefType t = refreshRefType' 2 t

refreshRefType' n (RAllT α t)
  = liftM (RAllT α) (refreshRefType' n t)
refreshRefType' n (RAllP π t)
  = liftM (RAllP π) (refreshRefType' n t)
refreshRefType' n (RFun b t t' _)
  | b == dummySymbol
  = liftM3 rFun fresh (refreshRefType' n t) (refreshRefType' n t')
  | otherwise
  = liftM2 (rFun b) (refreshRefType' n t) (refreshRefType' n t')
refreshRefType' n (RApp rc ts _ r)
  = do tyi                 <- getTyConInfo
       tce                 <- getTyConEmbed
       let RApp rc' _ rs _  = expandRApp tce tyi (RApp rc ts [] r)
       let rπs              = safeZip "refreshRef" rs (rTyConPs rc')
       liftM3 (RApp rc') (mapM (refreshRefType' n) ts) (mapM (refreshRef n) rπs) (refresh r)
refreshRefType' n (RVar a r)
  = liftM (RVar a) (refresh r)
refreshRefType' n (RAppTy t t' r)
  = liftM3 RAppTy (refreshRefType' n t) (refreshRefType' n t') (refresh r)
refreshRefType' n t
  = return t


refreshRef :: (Freshable m Integer, Freshable m r, TCInfo m, Reftable r)
           => Int
           -> (Ref RSort r (RRType r), PVar RSort)
           -> m (Ref RSort r (RRType r))

refreshRef 0 (RPoly s t, π) = liftM2 RPoly (mapM freshSym (pargs π)) (return t)
refreshRef n (RPoly s t, π) = liftM2 RPoly (mapM freshSym (pargs π)) (refreshRefType' (n-1) t)
refreshRef n (RMono _ _, _) = errorstar "refreshRef: unexpected"

freshSym s                = liftM (, fst3 s) fresh
