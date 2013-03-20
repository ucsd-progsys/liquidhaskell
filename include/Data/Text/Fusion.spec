module spec Data.Text.Fusion where

measure slen :: S.Stream a -> Int

stream        :: t:Text -> {v:S.Stream Char | (slen v) = (tlen t)}
reverseStream :: t:Text -> {v:S.Stream Char | (slen v) = (tlen t)}
unstream      :: s:S.Stream Char -> {v:Text | (tlen v) = (slen s)}

length  :: s:S.Stream Char -> {v:Int | v = (slen s)}
reverse :: s:S.Stream Char -> {v:Text | (tlen v) = (slen s)}
