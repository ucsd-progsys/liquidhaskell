module spec GHC.CString where

import GHC.Prim 

embed GHC.Prim.Addr# as String 
embed GHC.Types.Char as Char

GHC.CString.unpackCString#
  :: x:GHC.Prim.Addr#
  -> {v:[Char] | v ~~ x && stringLen x == stringLen v }
