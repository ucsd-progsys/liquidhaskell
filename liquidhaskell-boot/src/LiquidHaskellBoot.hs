module LiquidHaskellBoot (
    -- * LiquidHaskell Specification QuasiQuoter
    lq
    -- * LiquidHaskell as a compiler plugin
  , plugin
  ) where

import Language.Haskell.Liquid.UX.QuasiQuoter
import Language.Haskell.Liquid.GHC.Plugin (plugin)
