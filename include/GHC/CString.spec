module spec GHC.CString where

import GHC.Prim 

measure unpack :: GHC.Prim.Addr# -> String

GHC.CString.unpackCString# :: x:GHC.Prim.Addr# -> {v:String | v = unpack x}
