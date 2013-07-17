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
  fresh = liftM (`RKvar` emptySubst) freshK
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

trueRefType (RAllT α t)       
  = liftM (RAllT α) (true t)
trueRefType (RAllP π t)       
  = liftM (RAllP π) (true t)
trueRefType (RFun _ t t' _)    
  = liftM3 rFun fresh (true t) (true t')
trueRefType (RApp c ts _ _)  
  = liftM (\ts -> RApp c ts truerefs top) (mapM true ts)
		where truerefs = (RPoly []  . ofRSort . ptype) <$> (rTyConPs c)
trueRefType (RAppTy t t' _)    
  = liftM2 rAppTy (true t) (true t')
trueRefType t                
  = return t


refreshRefType :: (Freshable m Integer, Freshable m r, TCInfo m, Reftable r)
               => RRType r
               -> m (RRType r)
refreshRefType (RAllT α t)       
  = liftM (RAllT α) (refresh t)
refreshRefType (RAllP π t)       
  = liftM (RAllP π) (refresh t)
refreshRefType (RFun b t t' _)
  | b == dummySymbol -- b == (RB F.dummySymbol)
  = liftM3 rFun fresh (refresh t) (refresh t')
  | otherwise
  = liftM2 (rFun b) (refresh t) (refresh t')
refreshRefType (RApp rc ts _ r)  
  = do tyi                 <- getTyConInfo
       tce                 <- getTyConEmbed
       let RApp rc' _ rs _  = expandRApp tce tyi (RApp rc ts [] r)
       let rπs              = safeZip "refreshRef" rs (rTyConPs rc')
       liftM3 (RApp rc') (mapM refresh ts) (mapM refreshRef rπs) (refresh r)
refreshRefType (RVar a r)  
  = liftM (RVar a) (refresh r)
refreshRefType (RAppTy t t' _)  
  = liftM2 rAppTy (refresh t) (refresh t')
refreshRefType t                
  = return t

refreshRef :: (Freshable m Integer, Freshable m r, TCInfo m, Reftable r)
           => (Ref RSort r (RRType r), PVar RSort)
           -> m (Ref RSort r (RRType r))

refreshRef (RPoly s t, π) = liftM2 RPoly (mapM freshSym (pargs π)) (refreshRefType t)
refreshRef (RMono _ _, _) = errorstar "refreshRef: unexpected"

freshSym s                = liftM (, fst3 s) fresh
