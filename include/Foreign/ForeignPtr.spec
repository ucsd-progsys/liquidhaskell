module spec Foreign.ForeignPtr where

-- measure fplen :: ForeignPtr a -> GHC.Types.Int
-- invariant {v: ForeignPtr a | (fplen v) >= 0}
-- invariant {v: Ptr a        | (plen v)  >= 0}
-- type ForeignPtrN a N = {v: (ForeignPtrV a) | (fplen v) = N }
-- type ForeignPtrV a   = {v: (ForeignPtr  a) | 0 <= (fplen v)}

Foreign.ForeignPtr.Imp.withForeignPtr :: fp:(ForeignPtr a)
                                      -> ({v:(Foreign.Ptr.Ptr a) | (plen v) = (fplen fp)} -> IO b) 
                                      -> IO b

-- Foreign.ForeignPtr.withForeignPtr :: fp:(ForeignPtr a) 
--                                   -> ({v:(Ptr a) | (plen v) = (fplen fp)} -> IO b) 
--                                   -> IO b 


measure fplen :: GHC.ForeignPtr.ForeignPtr a -> GHC.Types.Int

type ForeignPtrV a   = {v: (ForeignPtr  a) | 0 <= (fplen v)}

type ForeignPtrN a N = {v: (ForeignPtrV a) | (fplen v) = N }


Foreign.ForeignPtr.withForeignPtr :: fp:(GHC.ForeignPtr.ForeignPtr a) -> ((PtrN a (fplen fp)) -> IO b) -> (IO b)
GHC.ForeignPtr.newForeignPtr_     :: p:(GHC.Ptr.Ptr a) -> (IO (ForeignPtrN a (plen p)))
Foreign.Concurrent.newForeignPtr  :: p:(PtrV a) -> IO () -> (IO (ForeignPtrN a (plen p)))

Foreign.ForeignPtr.newForeignPtr :: FinalizerPtr a -> p:(PtrV a) -> (IO (ForeignPtrN a (plen p)))
Foreign.ForeignPtr.Imp.newForeignPtr :: FinalizerPtr a -> p:(PtrV a) -> (IO (ForeignPtrN a (plen p)))

-- this uses `sizeOf (undefined :: a)`, so the ForeignPtr does not necessarily have length `n`
-- Foreign.ForeignPtr.Imp.mallocForeignPtrArray :: (Foreign.Storable.Storable a) => n:Nat -> IO (ForeignPtrN a n)
