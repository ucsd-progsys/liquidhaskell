-- | This module contains definitions that change between different versions
-- of the GHC API. It helps encapsulating differences between branches of LH
-- that could support different versions of GHC.
module Liquid.GHC.API.Compat (
    UniqueId
  , toUniqueId

  , foldableModule
  , realModule

  , foldl'
  ) where

import Data.Word (Word64)
import qualified GHC.Builtin.Names as Ghc
import GHC (Module)
import Data.List (foldl')

----------------------
-- Uniques
----------------------

type UniqueId = Int

toUniqueId :: Word64 -> UniqueId
toUniqueId = fromIntegral

----------------------
-- Built-in modules
----------------------

foldableModule, realModule :: Module

foldableModule = Ghc.dATA_FOLDABLE
realModule = Ghc.gHC_REAL
