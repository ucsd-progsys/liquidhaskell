module spec Foreign where

measure fplen :: GHC.ForeignPtr.ForeignPtr a -> GHC.Types.Int

-- invariant {v: ForeignPtr a | (fplen v) >= 0}

type ForeignPtrN a N = {v: (ForeignPtrV a) | (fplen v) = N }
type ForeignPtrV a   = {v: (GHC.ForeignPtr.ForeignPtr  a) | 0 <= (fplen v)}


