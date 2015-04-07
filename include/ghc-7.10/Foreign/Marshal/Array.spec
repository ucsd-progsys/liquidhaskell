module spec Foreign.Marshal.Array where

Foreign.Marshal.Array.allocaArray :: Foreign.Storable.Storable a => n:Int -> ((PtrN a n) -> IO b) -> IO b
