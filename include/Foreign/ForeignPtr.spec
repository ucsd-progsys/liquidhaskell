module spec Foreign.ForeignPtr where

measure fplen :: ForeignPtr a -> GHC.Types.Int

-- invariant {v: ForeignPtr a | (fplen v) >= 0}
-- invariant {v: Ptr a        | (plen v)  >= 0}

type ForeignPtrN a N = {v: (ForeignPtrV a) | (fplen v) = N }
type ForeignPtrV a   = {v: (ForeignPtr  a) | 0 <= (fplen v)}

Foreign.ForeignPtr.Imp.withForeignPtr :: fp:(ForeignPtr a) 
                                      -> ({v:(Foreign.Ptr.Ptr a) | (plen v) = (fplen fp)} -> IO b) 
                                      -> IO b

