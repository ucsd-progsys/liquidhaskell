-- | This module contains functions that convert things
--   to their `Bare` versions, e.g. SpecType -> BareType etc.

module Language.Haskell.Liquid.Bare.ToBare
  ( -- * Types
    specToBare

    -- * Measures
  , measureToBare
  )
  where

import           DataCon
import           Data.Bifunctor

import           Language.Fixpoint.Misc (mapSnd)
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Measure
import           Language.Haskell.Liquid.Types.RefType

--------------------------------------------------------------------------------
specToBare :: SpecType -> BareType
--------------------------------------------------------------------------------
specToBare = txRType specToBareTC specToBareTV

-- specToBare t = F.tracepp ("specToBare t2 = " ++ F.showpp t2)  t1
  -- where
    -- t1       = bareOfType . toType $ t
    -- t2       = _specToBare           t


--------------------------------------------------------------------------------
measureToBare :: SpecMeasure -> BareMeasure
--------------------------------------------------------------------------------
measureToBare = bimap (fmap specToBare) dataConToBare

dataConToBare :: DataCon -> LocSymbol
dataConToBare d = (dropModuleNames . F.symbol) <$> locNamedThing d
  where
    _msg  = "dataConToBare dc = " ++ show d ++ " v = " ++ show v ++ " vx = " ++ show vx
    v     = dataConWorkId d
    vx    = F.symbol v

specToBareTC :: RTyCon -> BTyCon
specToBareTC = tyConBTyCon . rtc_tc

specToBareTV :: RTyVar -> BTyVar
specToBareTV (RTV α) = BTV (F.symbol α)

txRType :: (c1 -> c2) -> (tv1 -> tv2) -> RType c1 tv1 r -> RType c2 tv2 r
txRType cF vF = go
  where
    -- go :: RType c1 tv1 r -> RType c2 tv2 r
    go (RVar α r)          = RVar  (vF α) r
    go (RAllT α t)         = RAllT (goRTV α) (go t)
    go (RAllP π t)         = RAllP (goPV  π) (go t)
    go (RAllS s t)         = RAllS s         (go t)
    go (RFun x t t' r)     = RFun  x         (go t) (go t') r
    go (RAllE x t t')      = RAllE x         (go t) (go t')
    go (REx x t t')        = REx   x         (go t) (go t')
    go (RAppTy t t' r)     = RAppTy          (go t) (go t') r
    go (RApp c ts rs r)    = RApp  (cF c)    (go <$> ts) (goRTP <$> rs) r
    go (RRTy xts r o t)    = RRTy  (mapSnd go <$> xts) r o (go t)
    go (RExprArg e)        = RExprArg e
    go (RHole r)           = RHole r

    -- go' :: RType c1 tv1 () -> RType c2 tv2 ()
    go' = txRType cF vF

    -- goRTP :: RTProp c1 tv1 r -> RTProp c2 tv2 r
    goRTP (RProp s (RHole r)) = RProp (mapSnd go' <$> s) (RHole r)
    goRTP (RProp s t)         = RProp (mapSnd go' <$> s) (go t)

    -- goRTV :: RTVU c1 tv1 -> RTVU c2 tv2
    goRTV = txRTV cF vF

    -- goPV :: PVU c1 tv1 -> PVU c2 tv2
    goPV = txPV cF vF

txRTV :: (c1 -> c2) -> (tv1 -> tv2) -> RTVU c1 tv1 -> RTVU c2 tv2
txRTV cF vF (RTVar α z) = RTVar (vF α) (txRType cF vF <$> z)

txPV :: (c1 -> c2) -> (tv1 -> tv2) -> PVU c1 tv1 -> PVU c2 tv2
txPV cF vF (PV x k y txes) = PV x k' y txes'
  where
    txes'                  = [ (tx t, x, e) | (t, x, e) <- txes]
    k'                     = tx <$> k
    tx                     = txRType cF vF
