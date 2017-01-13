
-- | This module contains functions that convert things to their `Bare` versions,
--   e.g. SpecType -> BareType etc.
module Language.Haskell.Liquid.Bare.ToBare
  ( -- * Types
    specToBare

    -- * Measures
  , measureToBare
  )
  where

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Measure

specToBare :: SpecType -> BareType
specToBare = error "TODO:specToBare"

measureToBare :: SpecMeasure -> BareMeasure
measureToBare = error "TODO:measureToBare"
