module spec GHC.CString where

// This was:
//import GHC.Prim
import GHC.Types

measure strLen :: GHC.Base.String -> GHC.Types.Int

GHC.CString.unpackCString#
  :: x:GHC.Prim.Addr#
  -> {v:[Char] | v ~~ x && len v == strLen x}
