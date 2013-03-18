module spec Foreign where

measure fplen :: ForeignPtr a -> GHC.Types.Int
measure plen  :: Ptr a        -> GHC.Types.Int

invariant {v: ForeignPtr a | (fplen v) >= 0}
invariant {v: Ptr a        | (plen v)  >= 0}

type ForeignPtrN a N = {v: ForeignPtr a | (fplen v) = N}
type PtrN a N        = {v: Ptr a        | (plen v)  = N}
