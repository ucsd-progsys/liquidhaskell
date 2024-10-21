{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.ByteString.Unsafe_LHAssumptions where

import Data.ByteString
import Data.ByteString.Unsafe
import Data.ByteString_LHAssumptions()
import GHC.Types_LHAssumptions()

{-@
assume Data.ByteString.Unsafe.unsafeHead
    :: { bs : ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.Unsafe.unsafeTail
    :: bs : { v : ByteString | bslen v > 0 }
    -> { v : ByteString | bslen v = bslen bs - 1 }

assume Data.ByteString.Unsafe.unsafeInit
    :: { bs : ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.Unsafe.unsafeLast
    :: { bs : ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.Unsafe.unsafeIndex
    :: bs : ByteString
    -> { n : Int | 0 <= n && n < bslen bs }
    -> _

assume Data.ByteString.Unsafe.unsafeTake
    :: n : { n : Int | 0 <= n }
    -> i : { i : ByteString | n <= bslen i }
    -> { o : ByteString | bslen o == n }

assume Data.ByteString.Unsafe.unsafeDrop
    :: n : { n : Int | 0 <= n }
    -> i : { i : ByteString | n <= bslen i }
    -> { o : ByteString | bslen o == bslen i - n }
@-}
