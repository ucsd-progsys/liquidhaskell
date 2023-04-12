{-# OPTIONS_GHC -Wno-unused-imports #-}
module Foreign.Marshal.Alloc_LHAssumptions where

import GHC.Types_LHAssumptions()
import GHC.Ptr_LHAssumptions()
import Foreign.Marshal.Alloc

{-@
Foreign.Marshal.Alloc.allocaBytes :: n:Nat -> (PtrN a n -> IO b) -> IO b
@-}
