module spec Data.Text.Fusion where

measure slen :: S.Stream a -> Int

stream        :: t:Text -> {v:S.Stream Char | (slen v) = (tlength t)}
reverseStream :: t:Text -> {v:S.Stream Char | (slen v) = (tlength t)}
unstream      :: s:S.Stream Char -> {v:Text | (tlength v) = (slen s)}

length  :: s:S.Stream Char -> {v:Int | v = (slen s)}
reverse :: s:S.Stream Char -> {v:Text | (tlength v) = (slen s)}
