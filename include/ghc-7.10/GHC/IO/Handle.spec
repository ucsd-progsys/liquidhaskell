module spec GHC.IO.Handle where

hGetBuf :: GHC.IO.Handle.Handle -> GHC.Ptr.Ptr a -> n:Nat
        -> (GHC.Types.IO {v:Nat | v <= n})

hGetBufNonBlocking :: GHC.IO.Handle.Handle -> GHC.Ptr.Ptr a -> n:Nat
                   -> (GHC.Types.IO {v:Nat | v <= n})

hFileSize :: GHC.IO.Handle.Handle
          -> (GHC.Types.IO {v:GHC.Integer.Type.Integer | v >= 0})
