{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Foreign.ForeignPtr_LHAssumptions where

import Foreign.Concurrent_LHAssumptions()
import Foreign.Storable
import GHC.ForeignPtr
import GHC.Internal.Foreign.ForeignPtr.Imp
import GHC.ForeignPtr_LHAssumptions()

{-@

assume GHC.Internal.ForeignPtr.withForeignPtr :: forall a b. fp:(ForeignPtr a)
  -> ((PtrN a (fplen fp)) -> IO b)
  -> IO b

assume GHC.Internal.Foreign.ForeignPtr.Imp.newForeignPtr ::  _ -> p:(PtrV a) -> (IO (ForeignPtrN a (plen p)))


//  this uses `sizeOf (undefined :: a)`, so the ForeignPtr does not necessarily have length `n`
//  Foreign.ForeignPtr.Imp.mallocForeignPtrArray :: (Foreign.Storable.Storable a) => n:Nat -> IO (ForeignPtrN a n)
@-}
