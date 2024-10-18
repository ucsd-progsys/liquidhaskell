-- | This module contains definitions that change between different versions
-- of the GHC API. It helps encapsulating differences between branches of LH
-- that could support different versions of GHC.
module Liquid.GHC.API.Compat (
    UniqueId
  , toUniqueId

  , foldableModule
  , realModule

  , mkHsTyConApp
  ) where

import Data.Word (Word64)
import qualified GHC.Builtin.Names as Ghc
import GHC (Module, LexicalFixity(..))
import GHC.Hs

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


----------------------
-- AST differences
----------------------

mkHsTyConApp ::  IdP GhcPs -> [LHsType GhcPs] -> LHsType GhcPs
mkHsTyConApp tyconId tyargs = nlHsTyConApp NotPromoted Prefix tyconId (map (HsValArg noExtField) tyargs)
