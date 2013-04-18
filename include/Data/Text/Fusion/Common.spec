module spec Data.Text.Fusion.Common where

cons :: Char
     -> s:Data.Text.Fusion.Internal.Stream Char
     -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) = (1 + (slen s))}
snoc :: s:Data.Text.Fusion.Internal.Stream Char
     -> Char
     -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) = (1 + (slen s))}

isSingleton :: s:Data.Text.Fusion.Internal.Stream Char
            -> {v:Bool | ((Prop v) <=> ((slen s) = 1))}
singleton   :: Char
            -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) = 1}

streamList   :: l:[a]
             -> {v:Data.Text.Fusion.Internal.Stream a | (slen v) = (len l)}
unstreamList :: s:Data.Text.Fusion.Internal.Stream a
             -> {v:[a] | (len v) = (slen s)}

map :: (Char -> Char)
    -> s:Data.Text.Fusion.Internal.Stream Char
    -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) = (slen s)}
filter :: (Char -> Bool)
       -> s:Data.Text.Fusion.Internal.Stream Char
       -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) <= (slen s)}

intersperse :: Char
            -> s:Data.Text.Fusion.Internal.Stream Char
            -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) > (slen s)}

replicateCharI :: l:Int
               -> Char
               -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) = l}

toCaseFold :: s:Data.Text.Fusion.Internal.Stream Char
           -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) >= (slen s)}
toUpper    :: s:Data.Text.Fusion.Internal.Stream Char
           -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) >= (slen s)}
toLower    :: s:Data.Text.Fusion.Internal.Stream Char
           -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) >= (slen s)}
