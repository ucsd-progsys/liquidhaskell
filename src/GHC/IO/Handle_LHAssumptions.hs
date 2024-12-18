{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.IO.Handle_LHAssumptions where

import GHC.IO.Handle
import GHC.Ptr
import GHC.Types_LHAssumptions()

{-@
assume hGetBuf :: Handle -> Ptr a -> n:Nat
        -> (IO {v:Nat | v <= n})

assume hGetBufNonBlocking :: Handle -> Ptr a -> n:Nat
                   -> (IO {v:Nat | v <= n})

assume hFileSize :: Handle
          -> (IO {v:Integer | v >= 0})
@-}
