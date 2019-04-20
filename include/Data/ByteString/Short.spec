module spec Data.ByteString.Short where

import Data.String

measure sbslen :: Data.ByteString.Short.ShortByteString -> { n : Int | 0 <= n }

invariant { bs : Data.ByteString.Short.ShortByteString  | 0 <= sbslen bs }

invariant { bs : Data.ByteString.Short.ShortByteString | sbslen bs == stringlen bs }

toShort :: i : Data.ByteString.ByteString -> { o : Data.ByteString.Short.ShortByteString | sbslen o == bslen i }

fromShort :: o : Data.ByteString.Short.ShortByteString -> { i : Data.ByteString.ByteString | bslen i == sbslen o }

pack :: w8s : [Data.Word.Word8] -> { bs : Data.ByteString.Short.ShortByteString | sbslen bs == len w8s }

unpack :: bs : Data.ByteString.Short.ShortByteString -> { w8s : [Data.Word.Word8] | len w8s == sbslen bs }

empty :: { bs : Data.ByteString.Short.ShortByteString | sbslen bs == 0 }

null :: bs : Data.ByteString.Short.ShortByteString -> { b : GHC.Types.Bool | b <=> sbslen bs == 0 }

length :: bs : Data.ByteString.Short.ShortByteString -> { n : Int | sbslen bs == n }

index :: bs : Data.ByteString.Short.ShortByteString -> { n : Int | 0 <= n && n < sbslen bs } -> Data.Word.Word8
