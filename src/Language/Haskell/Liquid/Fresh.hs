{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE OverloadedStrings     #-}

module Language.Haskell.Liquid.Fresh (
  Freshable(..), TCInfo(..)
  ) where

import Control.Monad.State
import Control.Applicative              (Applicative, (<$>), (<*>))

import qualified TyCon as TC

import qualified Data.HashMap.Strict as M

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.RefType  (uTop, expandRApp)
import Language.Fixpoint.Types
import Language.Fixpoint.Misc


import Data.Monoid                      (mempty)

type TTCInfo  = M.HashMap TC.TyCon RTyCon
type TTCEmbed = TCEmb TC.TyCon

class (Applicative m, Monad m) => Freshable m a where
  fresh   :: m a
  true    :: a -> m a
  true    = return . id
  refresh :: a -> m a
  refresh = return . id

class (Applicative m, Monad m) => TCInfo m where
  getTyConInfo  :: m TTCInfo
  getTyConInfo  = return $ M.empty
  getTyConEmbed :: m TTCEmbed
  getTyConEmbed = return $ M.empty

instance Freshable m Integer => Freshable m Symbol where
  fresh = tempSymbol "x" <$> fresh

instance Freshable m Integer => Freshable m Refa where
  fresh      = ((`RKvar` mkSubst []) . intKvar) <$> fresh
    -- where
      -- freshK = intKvar <$> fresh

instance Freshable m Integer => Freshable m [Refa] where
  fresh = single <$> fresh

-- instance Monad m => Freshable m TCEmbed where

instance Freshable m Integer => Freshable m Reft where
  fresh                = errorstar "fresh Reft"
  true    (Reft (v,_)) = return $ Reft (v, []) 
  refresh (Reft (_,_)) = (Reft .) . (,) <$> freshVV <*> fresh
    where
      freshVV          = vv . Just <$> fresh

instance Freshable m Integer => Freshable m RReft where
  fresh             = errorstar "fresh RReft"
  true (U r _ s)    = U <$> true r    <*> return mempty <*> true s 
  refresh (U r _ s) = U <$> refresh r <*> return mempty <*> refresh s

instance Freshable m Integer => Freshable m Strata where
  fresh      = (:[]) . SVar <$> fresh           
  true []    = fresh
  true s     = return s
  refresh [] = fresh
  refresh s  = return s

instance (Freshable m Integer, Freshable m r, TCInfo m, Reftable r) => Freshable m (RRType r) where
  fresh   = errorstar "fresh RefType"
  refresh = refreshRefType
  true    = trueRefType 

trueRefType :: (Freshable m Integer, Freshable m r,TCInfo m,  Reftable r) => RRType r -> m (RRType r)
trueRefType (RAllT α t)       
  = RAllT α <$> true t
trueRefType (RAllP π t)       
  = RAllP π <$> true t
trueRefType (RFun _ t t' _)    
  = rFun <$> fresh <*> true t <*> true t'
trueRefType (RApp c ts _ r)  
  = (\ts -> RApp c ts truerefs) <$> mapM true ts <*> true r
    where truerefs = (RProp []  . ofRSort . pvType) <$> (rTyConPropVs c)
trueRefType (RAppTy t t' _)    
  = RAppTy <$> true t <*> true t' <*> return mempty
trueRefType (RVar a r)
  = RVar a <$> true r
trueRefType t                
  = return t


refreshRefType :: (Freshable m Integer, Freshable m r, TCInfo m, Reftable r)
               => RRType r
               -> m (RRType r)
refreshRefType (RAllT α t)       
  = RAllT α <$> refresh t

refreshRefType (RAllP π t)       
  = RAllP π <$> refresh t

refreshRefType (RFun b t t' _)
  | b == dummySymbol
  = rFun <$> fresh <*> refresh t <*> refresh t'
  | otherwise
  = rFun b <$> refresh t <*> refresh t'

refreshRefType (RApp rc ts _ r)  
  = do tyi                 <- getTyConInfo
       tce                 <- getTyConEmbed
       let RApp rc' _ rs _  = expandRApp tce tyi (RApp rc ts [] r)
       let rπs              = safeZip "refreshRef" rs (rTyConPVs rc')
       RApp rc' <$> mapM refresh ts <*> mapM refreshRef rπs <*> refresh r

-- EFFECTS refreshRefType (RApp rc ts rs r)  
-- EFFECTS   = RApp rc <$> mapM refresh ts <*> mapM refreshRef rs <*> refresh r

refreshRefType (RVar a r)  
  = RVar a <$> refresh r
    
refreshRefType (RAppTy t t' r)  
  = RAppTy <$> refresh t <*> refresh t' <*> refresh r
    
refreshRefType t                
  = return t

-- EFFECTS refreshRef (RProp s t) = RProp <$> mapM freshSym s <*> refreshRefType t
-- EFFECTS refreshRef _           = errorstar "refreshRef: unexpected"
-- EFFECTS freshSym (_, t)        = (, t) <$> fresh 

refreshRef :: (Freshable m Integer, Freshable m r, TCInfo m, Reftable r)
           => (RRProp r, PVar RSort)
           -> m (RRProp r)

refreshRef (RProp s t, π) = RProp <$> mapM freshSym (pargs π) <*> refreshRefType t
refreshRef _              = errorstar "refreshRef: unexpected"
freshSym s                = (, fst3 s) <$> fresh
