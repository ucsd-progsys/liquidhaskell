module spec Foreign.Ptr where

measure plen  :: Foreign.Ptr a -> GHC.Types.Int

type PtrN a N = {v: (PtrV a)        | (plen v)  = N }
type PtrV a   = {v: (Ptr a)         | 0 <= (plen v) } 


-- import GHC.Ptr
-- type PtrV a          = {v: (Foreign.Ptr.Ptr a)  | 0 <= (plen v) } 
-- measure plen         :: Foreign.Ptr.Ptr a -> GHC.Types.Int
-- invariant {v: Ptr a        | (plen v)  >= 0}


