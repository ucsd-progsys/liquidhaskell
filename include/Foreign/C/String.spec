module spec Foreign.C.String where

import Foreign.Ptr

type CStringLen    = ((GHC.Ptr.Ptr Foreign.C.Types.CChar), Nat)<{\p v -> (v <= (plen p))}>
type CStringLenN N = ((GHC.Ptr.Ptr Foreign.C.Types.CChar), {v:Nat | v = N})<{\p v -> (v <= (plen p))}>

measure cStringLen :: Foreign.C.String.CStringLen -> GHC.Types.Int
cStringLen (c, n) = n
