module spec Data.Text.Lazy.Fusion where

stream :: t:Data.Text.Internal.Lazy.Text
       -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) = (ltlength t)}
unstream :: s:Data.Text.Fusion.Internal.Stream Char
         -> {v:Data.Text.Internal.Lazy.Text | (ltlength v) = (slen s)}
length :: s:Data.Text.Fusion.Internal.Stream Char
       -> {v:Int64 | v = (slen s)}
