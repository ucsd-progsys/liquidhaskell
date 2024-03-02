{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.IO.Handle_LHAssumptions where

import GHC.IO.Handle
import GHC.Types_LHAssumptions()

{-@
assume GHC.Internal.IO.Handle.Text.hGetBuf :: GHC.Internal.IO.Handle.Handle -> GHC.Internal.Ptr.Ptr a -> n:Nat
        -> (GHC.Types.IO {v:Nat | v <= n})

assume GHC.Internal.IO.Handle.Text.hGetBufNonBlocking :: GHC.Internal.IO.Handle.Handle -> GHC.Internal.Ptr.Ptr a -> n:Nat
                   -> (GHC.Types.IO {v:Nat | v <= n})

assume GHC.Internal.IO.Handle.hFileSize :: GHC.Internal.IO.Handle.Handle
          -> (GHC.Types.IO {v:Integer | v >= 0})
@-}
