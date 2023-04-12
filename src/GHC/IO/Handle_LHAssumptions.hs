{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.IO.Handle_LHAssumptions where

import GHC.IO.Handle
import GHC.Types_LHAssumptions()

{-@
assume GHC.IO.Handle.hGetBuf :: GHC.IO.Handle.Handle -> GHC.Ptr.Ptr a -> n:Nat
        -> (GHC.Types.IO {v:Nat | v <= n})

assume GHC.IO.Handle.hGetBufNonBlocking :: GHC.IO.Handle.Handle -> GHC.Ptr.Ptr a -> n:Nat
                   -> (GHC.Types.IO {v:Nat | v <= n})

assume GHC.IO.Handle.hFileSize :: GHC.IO.Handle.Handle
          -> (GHC.Types.IO {v:Integer | v >= 0})
@-}
