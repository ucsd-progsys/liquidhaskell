{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.ByteString.Short_LHAssumptions where

import Data.ByteString
import Data.ByteString_LHAssumptions()
import Data.ByteString.Short
import Data.String_LHAssumptions()
import Data.Word

{-@
measure sbslen :: ShortByteString -> { n : Int | 0 <= n }

invariant { bs : ShortByteString  | 0 <= sbslen bs }

invariant { bs : ShortByteString | sbslen bs == stringlen bs }

assume Data.ByteString.Short.Internal.toShort :: i : ByteString -> { o : ShortByteString | sbslen o == bslen i }

assume Data.ByteString.Short.Internal.fromShort :: o : ShortByteString -> { i : ByteString | bslen i == sbslen o }

assume Data.ByteString.Short.Internal.pack :: w8s : [Word8] -> { bs : ShortByteString | sbslen bs == len w8s }

assume Data.ByteString.Short.Internal.unpack :: bs : ShortByteString -> { w8s : [Word8] | len w8s == sbslen bs }

assume Data.ByteString.Short.Internal.empty :: { bs : ShortByteString | sbslen bs == 0 }

assume Data.ByteString.Short.Internal.null :: bs : ShortByteString -> { b : Bool | b <=> sbslen bs == 0 }

assume Data.ByteString.Short.Internal.length :: bs : ShortByteString -> { n : Int | sbslen bs == n }

assume Data.ByteString.Short.Internal.index :: bs : ShortByteString -> { n : Int | 0 <= n && n < sbslen bs } -> Word8
@-}
