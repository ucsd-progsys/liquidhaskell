import Data.ByteString
import Data.ByteString.Unsafe

{-@ assume unsafeTake :: n : Int -> ibs : { ibs : ByteString | bslen ibs >= n } -> { obs : ByteString | bslen obs == n } @-}
{-@ assume unsafeDrop :: n : Int -> ibs : { ibs : ByteString | bslen ibs >= n } -> { obs : ByteString | bslen obs == bslen ibs - n } @-}


{-@ extract :: ibs : { ibs : ByteString | bslen ibs >= 100 } -> { obs : ByteString | bslen obs == 4 } @-}
extract :: ByteString -> ByteString
extract = unsafeTake 4 . unsafeDrop 96

{-@ extractETA :: ibs : { ibs : ByteString | bslen ibs >= 100 } -> { obs : ByteString | bslen obs == 4 } @-}
extractETA :: ByteString -> ByteString
extractETA ibs = unsafeTake 4 (unsafeDrop 96 ibs)

{-@ ok :: x:Int -> {v:Int | v == x + 3} @-}
ok :: Int -> Int
ok x = 2 + (1 + x)

{-@ bad :: x:Int -> {v:Int | v == x + 3} @-}
bad :: Int -> Int
bad = (2 +) . (1 +)
