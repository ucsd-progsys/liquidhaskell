module spec Data.Text.Fusion.Common where

cons :: Char -> s:S.Stream Char -> {v:S.Stream Char | (slen v) > (slen s)}
snoc :: s:S.Stream Char -> Char -> {v:S.Stream Char | (slen v) > (slen s)}

isSingleton :: s:S.Stream Char -> {v:Bool | ((Prop v) <=> ((slen s) = 1))}
singleton   :: Char -> {v:S.Stream Char | (slen v) = 1}

streamList   :: l:[a] -> {v:S.Stream a | (slen v) = (len l)}
unstreamList :: s:S.Stream a -> {v:[a] | (len v) = (slen s)}

map :: (Char -> Char) -> s:S.Stream Char -> {v:S.Stream Char | (slen v) = (slen s)}

intersperse :: Char -> s:S.Stream Char -> {v:S.Stream Char | (slen v) > (slen s)}

replicateCharI :: Integral a => l:a -> Char -> {v:S.Stream Char | (slen v) = l}
