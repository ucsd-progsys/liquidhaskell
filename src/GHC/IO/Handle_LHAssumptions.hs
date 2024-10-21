{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.IO.Handle_LHAssumptions where

import GHC.IO.Handle
import GHC.Ptr
import GHC.Types_LHAssumptions()

{-@
assume GHC.Internal.IO.Handle.Text.hGetBuf :: Handle -> Ptr a -> n:Nat
        -> (IO {v:Nat | v <= n})

assume GHC.Internal.IO.Handle.Text.hGetBufNonBlocking :: Handle -> Ptr a -> n:Nat
                   -> (IO {v:Nat | v <= n})

assume GHC.Internal.IO.Handle.hFileSize :: Handle
          -> (IO {v:Integer | v >= 0})
@-}
