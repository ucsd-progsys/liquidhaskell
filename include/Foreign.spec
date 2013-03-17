module spec Foreign where

measure plen :: ForeignPtr a -> GHC.Types.Int

invariant {v: ForeignPtr a | (plen v) >= 0}

type ForeignPtrN a N = {v: ForeignPtr a | (plen v) = N}
