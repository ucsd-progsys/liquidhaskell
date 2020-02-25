module spec GHC.CString where

import GHC.Prim
import GHC.Types

measure strLen :: [Char] -> GHC.Types.Int

GHC.CString.unpackCString#
  :: x:GHC.Prim.Addr#
  -> {v:[Char] | v ~~ x && strLen v == addrLen x}
