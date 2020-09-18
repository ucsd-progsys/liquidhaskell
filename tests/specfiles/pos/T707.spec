module spec T707 where

uncons
    :: i : Data.ByteString.ByteString
    -> Maybe (Data.Word.Word8, { o : Data.ByteString.ByteString | bslen o == bslen i - 1 })

unsnoc
    :: i : Data.ByteString.ByteString
    -> Maybe ({ o : Data.ByteString.ByteString | bslen o == bslen i - 1 }, Data.Word.Word8)

uncons'
    :: i : Data.ByteString.ByteString
    -> (Maybe (Data.Word.Word8, { o : Data.ByteString.ByteString | bslen o == bslen i - 1 }))

unsnoc'
    :: i : Data.ByteString.ByteString
    -> (Maybe ({ o : Data.ByteString.ByteString | bslen o == bslen i - 1 }, Data.Word.Word8))
