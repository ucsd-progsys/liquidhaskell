{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.ByteString.Unsafe_LHAssumptions where

import Data.ByteString.Unsafe
import Data.ByteString_LHAssumptions()
import GHC.Types_LHAssumptions()

{-@
assume Data.ByteString.Unsafe.unsafeHead
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.Unsafe.unsafeTail
    :: bs : { v : Data.ByteString.ByteString | bslen v > 0 }
    -> { v : Data.ByteString.ByteString | bslen v = bslen bs - 1 }

assume Data.ByteString.Unsafe.unsafeInit
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.Unsafe.unsafeLast
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.Unsafe.unsafeIndex
    :: bs : Data.ByteString.ByteString
    -> { n : Int | 0 <= n && n < bslen bs }
    -> _

assume Data.ByteString.Unsafe.unsafeTake
    :: n : { n : Int | 0 <= n }
    -> i : { i : Data.ByteString.ByteString | n <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == n }

assume Data.ByteString.Unsafe.unsafeDrop
    :: n : { n : Int | 0 <= n }
    -> i : { i : Data.ByteString.ByteString | n <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == bslen i - n }
@-}
