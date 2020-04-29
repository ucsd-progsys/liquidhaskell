module spec Foreign.Marshal.Alloc where

Foreign.Marshal.Alloc.allocaBytes :: n:Nat -> (PtrN a n -> IO b) -> IO b
