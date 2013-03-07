module spec Data.Text.Fusion where

measure slen :: S.Stream a -> Int

assume stream :: t:Text -> {v:S.Stream Char | ((slen v) = (tlen t))}
assume unstream :: s:S.Stream Char -> {v:Text | ((tlen v) = (slen s))}
assume reverseStream :: t:Text -> {v:S.Stream Char | ((slen v) = (tlen t))}
