
-- | This module contains functions that convert things to their `Bare` versions,
--   e.g. SpecType -> BareType etc.
module Language.Haskell.Liquid.Bare.ToBare
  ( -- * Types
    specToBare

    -- * Measures
  , measureToBare
  )
  where

import           DataCon
import           Data.Bifunctor
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Measure


dataConToBare :: DataCon -> LocSymbol
dataConToBare d = Loc l e x
  where
    l           = getSourcePos  d
    e           = getSourcePosE d
    x           = dropModuleUnique (F.symbol d)

measureToBare :: SpecMeasure -> BareMeasure
measureToBare = bimap (fmap specToBare) dataConToBare

specToBare :: RRType r -> BRType r
specToBare = error "TODO:specToBare"
