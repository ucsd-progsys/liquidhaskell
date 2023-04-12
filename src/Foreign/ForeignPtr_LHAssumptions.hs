{-# OPTIONS_GHC -Wno-unused-imports #-}
module Foreign.ForeignPtr_LHAssumptions where

import Foreign.Concurrent_LHAssumptions()
import Foreign.ForeignPtr
import GHC.ForeignPtr_LHAssumptions()

{-@

assume GHC.ForeignPtr.withForeignPtr :: forall a b. fp:(GHC.ForeignPtr.ForeignPtr a)
  -> ((PtrN a (fplen fp)) -> GHC.Types.IO b)
  -> (GHC.Types.IO b)

assume Foreign.ForeignPtr.newForeignPtr ::  _ -> p:(PtrV a) -> (GHC.Types.IO (ForeignPtrN a (plen p)))


//  this uses `sizeOf (undefined :: a)`, so the ForeignPtr does not necessarily have length `n`
//  Foreign.ForeignPtr.Imp.mallocForeignPtrArray :: (Foreign.Storable.Storable a) => n:Nat -> IO (ForeignPtrN a n)
@-}
