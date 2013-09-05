module spec Data.Text.Fusion.Common where

measure slen :: Data.Text.Fusion.Internal.Stream a
             -> GHC.Types.Int

cons :: GHC.Types.Char
     -> s:Data.Text.Fusion.Internal.Stream Char
     -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) = (1 + (slen s))}
snoc :: s:Data.Text.Fusion.Internal.Stream Char
     -> GHC.Types.Char
     -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) = (1 + (slen s))}

compareLengthI :: s:Data.Text.Fusion.Internal.Stream Char
               -> l:GHC.Types.Int
               -> {v:GHC.Types.Ordering | ((v = GHC.Types.EQ) <=> ((slen s) = l))}

isSingleton :: s:Data.Text.Fusion.Internal.Stream Char
            -> {v:GHC.Types.Bool | ((Prop v) <=> ((slen s) = 1))}
singleton   :: GHC.Types.Char
            -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) = 1}

streamList   :: l:[a]
             -> {v:Data.Text.Fusion.Internal.Stream a | (slen v) = (len l)}
unstreamList :: s:Data.Text.Fusion.Internal.Stream a
             -> {v:[a] | (len v) = (slen s)}

map :: (GHC.Types.Char -> GHC.Types.Char)
    -> s:Data.Text.Fusion.Internal.Stream Char
    -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) = (slen s)}
filter :: (GHC.Types.Char -> GHC.Types.Bool)
       -> s:Data.Text.Fusion.Internal.Stream Char
       -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) <= (slen s)}

intersperse :: GHC.Types.Char
            -> s:Data.Text.Fusion.Internal.Stream Char
            -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) > (slen s)}

replicateCharI :: l:GHC.Types.Int
               -> GHC.Types.Char
               -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) = l}

toCaseFold :: s:Data.Text.Fusion.Internal.Stream Char
           -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) >= (slen s)}
toUpper    :: s:Data.Text.Fusion.Internal.Stream Char
           -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) >= (slen s)}
toLower    :: s:Data.Text.Fusion.Internal.Stream Char
           -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) >= (slen s)}
