module spec GHC.CString where

import GHC.Prim 

measure strLen :: GHC.Base.String -> GHC.Types.Int
embed GHC.Types.Char as Char

GHC.CString.unpackCString#
  :: x:GHC.Prim.Addr#
  -> {v:[Char] | v ~~ x && len v == strLen x}
