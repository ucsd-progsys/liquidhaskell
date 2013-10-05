module spec Foreign.Ptr where

import GHC.Ptr

measure pbase     :: Foreign.Ptr.Ptr a -> GHC.Types.Int
measure plen      :: Foreign.Ptr.Ptr a -> GHC.Types.Int
measure isNullPtr :: Foreign.Ptr.Ptr a -> Prop

type PtrN a N = {v: (PtrV a)        | (plen v)  = N }
type PtrV a   = {v: (GHC.Ptr.Ptr a) | 0 <= (plen v) }
