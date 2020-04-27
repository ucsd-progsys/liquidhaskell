module spec GHC.CString where

import GHC.Prim
import GHC.Types

measure strLen :: Addr# -> GHC.Types.Int

GHC.CString.unpackCString#
  :: x:GHC.Prim.Addr#
  -> {v:[Char] | v ~~ x && len v == strLen x}
