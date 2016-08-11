module spec Foreign.ForeignPtr where

import GHC.ForeignPtr
import Foreign.Ptr

Foreign.ForeignPtr.withForeignPtr :: fp:(GHC.ForeignPtr.ForeignPtr a) 
  -> ((PtrN a (fplen fp)) -> GHC.Types.IO b) 
  -> (GHC.Types.IO b)
GHC.ForeignPtr.newForeignPtr_     :: p:(GHC.Ptr.Ptr a) -> (GHC.Types.IO (ForeignPtrN a (plen p)))
Foreign.Concurrent.newForeignPtr  :: p:(PtrV a) -> GHC.Types.IO () -> (GHC.Types.IO (ForeignPtrN a (plen p)))

Foreign.ForeignPtr.newForeignPtr :: Foreign.ForeignPtr.FinalizerPtr a -> p:(PtrV a) -> (GHC.Types.IO (ForeignPtrN a (plen p)))

// this uses `sizeOf (undefined :: a)`, so the ForeignPtr does not necessarily have length `n`
// Foreign.ForeignPtr.Imp.mallocForeignPtrArray :: (Foreign.Storable.Storable a) => n:Nat -> IO (ForeignPtrN a n)
