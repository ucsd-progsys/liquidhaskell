module spec Foreign.Concurrent where

Foreign.Concurrent.newForeignPtr  :: p:(PtrV a) -> GHC.Types.IO () -> (GHC.Types.IO (ForeignPtrN a (plen p)))
