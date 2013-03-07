module spec Data.Text.Fusion.Common where

assume cons :: Char -> s:S.Stream Char -> {v:S.Stream Char | ((slen v) > (slen s))}
assume snoc :: s:S.Stream Char -> Char -> {v:S.Stream Char | ((slen v) > (slen s))}

assume singleton :: Char -> {v:S.Stream Char | (slen v) = 1}
assume streamList :: l:[a] -> {v:S.Stream a | ((slen v) = (len l))}
assume unstreamList :: s:S.Stream a -> {v:[a] | ((len v) = (slen s))}
