{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Foreign.Concurrent_LHAssumptions where

import Foreign.Concurrent
import GHC.ForeignPtr_LHAssumptions()

{-@
assume GHC.Internal.Foreign.Concurrent.newForeignPtr  :: p:(PtrV a) -> IO () -> (IO (ForeignPtrN a (plen p)))
@-}
