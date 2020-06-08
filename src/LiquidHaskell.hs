{-# LANGUAGE CPP #-}

module LiquidHaskell (
    -- * LiquidHaskell Specification QuasiQuoter
    lq
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,10,0,0)
    -- * LiquidHaskell as a compiler plugin
  , plugin
#endif
#endif
  ) where

import Language.Haskell.Liquid.UX.QuasiQuoter

#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,10,0,0)
import Language.Haskell.Liquid.GHC.Plugin (plugin)
#endif
#endif
