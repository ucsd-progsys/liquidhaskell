{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.ByteString.Short_LHAssumptions where

import Data.ByteString
import Data.ByteString_LHAssumptions()
import Data.ByteString.Short
import Data.String_LHAssumptions()

{-@
measure sbslen :: Data.ByteString.Short.ShortByteString -> { n : Int | 0 <= n }

invariant { bs : Data.ByteString.Short.ShortByteString  | 0 <= sbslen bs }

invariant { bs : Data.ByteString.Short.ShortByteString | sbslen bs == stringlen bs }

assume Data.ByteString.Short.Internal.toShort :: i : Data.ByteString.ByteString -> { o : Data.ByteString.Short.ShortByteString | sbslen o == bslen i }

assume Data.ByteString.Short.Internal.fromShort :: o : Data.ByteString.Short.ShortByteString -> { i : Data.ByteString.ByteString | bslen i == sbslen o }

assume Data.ByteString.Short.Internal.pack :: w8s : [Word8] -> { bs : Data.ByteString.Short.ShortByteString | sbslen bs == len w8s }

assume Data.ByteString.Short.Internal.unpack :: bs : Data.ByteString.Short.ShortByteString -> { w8s : [Word8] | len w8s == sbslen bs }

assume Data.ByteString.Short.Internal.empty :: { bs : Data.ByteString.Short.ShortByteString | sbslen bs == 0 }

assume Data.ByteString.Short.Internal.null :: bs : Data.ByteString.Short.ShortByteString -> { b : GHC.Types.Bool | b <=> sbslen bs == 0 }

assume Data.ByteString.Short.Internal.length :: bs : Data.ByteString.Short.ShortByteString -> { n : Int | sbslen bs == n }

assume Data.ByteString.Short.Internal.index :: bs : Data.ByteString.Short.ShortByteString -> { n : Int | 0 <= n && n < sbslen bs } -> Word8
@-}
