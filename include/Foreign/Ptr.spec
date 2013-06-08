module spec Foreign.Ptr where

import GHC.Ptr

measure plen         :: Foreign.Ptr.Ptr a -> GHC.Types.Int

type PtrN a N        = {v: (PtrV a)             | (plen v)  = N }
type PtrV a          = {v: (Foreign.Ptr.Ptr a)  | 0 <= (plen v) } 


