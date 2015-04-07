module spec GHC.CString where

import GHC.Prim 

GHC.CString.unpackCString# :: x:GHC.Prim.Addr# -> {v:String | v ~~ x}
