module spec Data.Text.Lazy.Fusion where

stream :: t:Data.Text.Lazy.Internal.Text
       -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) = (ltlength t)}
unstream :: s:Data.Text.Fusion.Internal.Stream Char
         -> {v:Data.Text.Lazy.Internal.Text | (ltlength v) = (slen s)}
length :: s:Data.Text.Fusion.Internal.Stream Char
       -> {v:GHC.Int.Int64 | v = (slen s)}
