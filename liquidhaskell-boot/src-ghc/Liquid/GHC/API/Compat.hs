-- | This module contains definitions that change between different versions
-- of the GHC API. It helps encapsulating differences between branches of LH
-- that could support different versions of GHC.
module Liquid.GHC.API.Compat (
    UniqueId
  , toUniqueId

  , foldableModule
  , realModule
  ) where

import Data.Word (Word64)
import qualified GHC.Builtin.Names as Ghc
import GHC (Module)

----------------------
-- Uniques
----------------------

type UniqueId = Word64

toUniqueId :: Word64 -> UniqueId
toUniqueId = id

----------------------
-- Built-in modules
----------------------

foldableModule, realModule :: Module

foldableModule = Ghc.gHC_INTERNAL_DATA_FOLDABLE
realModule = Ghc.gHC_INTERNAL_REAL
