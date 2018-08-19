module spec Data.ByteString.Unsafe where

unsafeHead
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _ 

unsafeTail
    :: bs : { v : Data.ByteString.ByteString | bslen v > 0 }
    -> { v : Data.ByteString.ByteString | bslen v = bslen bs - 1 }

unsafeInit
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _ 

unsafeLast
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _ 

unsafeIndex
    :: bs : Data.ByteString.ByteString
    -> { n : Int | 0 <= n && n < bslen bs }
    -> _ 

assume unsafeTake
    :: n : { n : Int | 0 <= n }
    -> i : { i : Data.ByteString.ByteString | n <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == n }

assume unsafeDrop
    :: n : { n : Int | 0 <= n }
    -> i : { i : Data.ByteString.ByteString | n <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == bslen i - n }
