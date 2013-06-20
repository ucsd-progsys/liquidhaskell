module spec Foreign.ForeignPtr where

-- measure fplen :: ForeignPtr a -> GHC.Types.Int
-- invariant {v: ForeignPtr a | (fplen v) >= 0}
-- invariant {v: Ptr a        | (plen v)  >= 0}
-- type ForeignPtrN a N = {v: (ForeignPtrV a) | (fplen v) = N }
-- type ForeignPtrV a   = {v: (ForeignPtr  a) | 0 <= (fplen v)}

-- Foreign.ForeignPtr.Imp.withForeignPtr :: fp:(ForeignPtr a) 
--                                       -> ({v:(Foreign.Ptr.Ptr a) | (plen v) = (fplen fp)} -> IO b) 
--                                       -> IO b
--
-- Foreign.ForeignPtr.withForeignPtr :: fp:(ForeignPtr a) 
--                                   -> ({v:(Ptr a) | (plen v) = (fplen fp)} -> IO b) 
--                                   -> IO b 

Foreign.ForeignPtr.withForeignPtr :: fp:(ForeignPtr a) -> ((PtrN a (fplen fp)) -> IO b) -> (IO b)
GHC.ForeignPtr.newForeignPtr_     :: p:(Ptr a) -> (IO (ForeignPtrN a (plen p)))
Foreign.Concurrent.newForeignPtr  :: p:(PtrV a) -> IO () -> (IO (ForeignPtrN a (plen p)))

Foreign.ForeignPtr.newForeignPtr :: FinalizerPtr a -> p:(PtrV a) -> (IO (ForeignPtrN a (plen p)))


