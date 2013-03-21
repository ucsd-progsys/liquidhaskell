module spec Foreign where

measure fplen :: ForeignPtr a -> GHC.Types.Int
measure plen  :: Ptr a        -> GHC.Types.Int

-- invariant {v: ForeignPtr a | (fplen v) >= 0}
-- invariant {v: Ptr a        | (plen v)  >= 0}

type ForeignPtrN a N = {v: (ForeignPtrV a) | (fplen v) = N }
type ForeignPtrV a   = {v: (ForeignPtr  a) | 0 <= (fplen v)}
type PtrN a N        = {v: (PtrV a)        | (plen v)  = N }
type PtrV a          = {v: (Ptr a)         | 0 <= (plen v) } 

