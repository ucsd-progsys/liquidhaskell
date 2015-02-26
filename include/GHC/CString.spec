module spec GHC.CString where

import GHC.Prim 

-- The equality is untyped, but there is an implicit logic cast
GHC.CString.unpackCString# :: x:GHC.Prim.Addr# -> {v:String | v = x}

