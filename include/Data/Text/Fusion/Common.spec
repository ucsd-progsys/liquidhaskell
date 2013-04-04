module spec Data.Text.Fusion.Common where

cons :: Char -> s:S.Stream Char -> {v:S.Stream Char | (slen v) = (1 + (slen s))}
snoc :: s:S.Stream Char -> Char -> {v:S.Stream Char | (slen v) = (1 + (slen s))}

isSingleton :: s:S.Stream Char -> {v:Bool | ((Prop v) <=> ((slen s) = 1))}
singleton   :: Char -> {v:S.Stream Char | (slen v) = 1}

streamList   :: l:[a] -> {v:S.Stream a | (slen v) = (len l)}
unstreamList :: s:S.Stream a -> {v:[a] | (len v) = (slen s)}

map :: (Char -> Char) -> s:S.Stream Char -> {v:S.Stream Char | (slen v) = (slen s)}
filter :: (Char -> Bool) -> s:S.Stream Char -> {v:S.Stream Char | (slen v) <= (slen s)}

intersperse :: Char -> s:S.Stream Char -> {v:S.Stream Char | (slen v) > (slen s)}

replicateCharI :: l:Int -> Char -> {v:S.Stream Char | (slen v) = l}

toCaseFold :: s:S.Stream Char -> {v:S.Stream Char | (slen v) >= (slen s)}
toUpper    :: s:S.Stream Char -> {v:S.Stream Char | (slen v) >= (slen s)}
toLower    :: s:S.Stream Char -> {v:S.Stream Char | (slen v) >= (slen s)}
