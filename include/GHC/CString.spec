module spec GHC.CString where

import GHC.Prim 

GHC.CString.unpackCString#
  :: x:GHC.Prim.Addr#
  -> {v:[Char] | v ~~ x && len v == strLen x}
