{-# OPTIONS_GHC -Wno-unused-imports #-}
module Foreign.Concurrent_LHAssumptions where

import Foreign.Concurrent
import GHC.ForeignPtr_LHAssumptions()

{-@
Foreign.Concurrent.newForeignPtr  :: p:(PtrV a) -> GHC.Types.IO () -> (GHC.Types.IO (ForeignPtrN a (plen p)))
@-}
