module spec GHC.CString where

import GHC.Prim 

GHC.CString.unpackCString#
  :: x:GHC.Prim.Addr#
  -> {v:String | len v == strLen x}
