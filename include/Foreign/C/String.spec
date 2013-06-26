module spec Foreign.C.String where

import Foreign.Ptr

type CStringLen    = ((Ptr Foreign.C.Types.CChar), Nat)<{\p v -> (v <= (plen p))}> 
type CStringLenN N = ((Ptr Foreign.C.Types.CChar), {v:Nat | v = N})<{\p v -> (v <= (plen p))}>


