module Liquid.GHC.API.Compat (
    UniqueId
  , toUniqueId
  ) where

import Data.Word (Word64)

----------------------
-- Uniques
----------------------

type UniqueId = Word64

toUniqueId :: Word64 -> UniqueId
toUniqueId = id
