module spec Foreign where

measure fplen :: ForeignPtr a -> GHC.Types.Int

-- invariant {v: ForeignPtr a | (fplen v) >= 0}

type ForeignPtrN a N = {v: (ForeignPtrV a) | (fplen v) = N }
type ForeignPtrV a   = {v: (ForeignPtr  a) | 0 <= (fplen v)}


