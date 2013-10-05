module spec Data.Text.Fusion where

import Data.Text.Fusion.Common

stream        :: t:Data.Text.Internal.Text
              -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) = (tlength t)}
reverseStream :: t:Data.Text.Internal.Text
              -> {v:Data.Text.Fusion.Internal.Stream Char | (slen v) = (tlength t)}
unstream      :: s:Data.Text.Fusion.Internal.Stream Char
              -> {v:Data.Text.Internal.Text | (tlength v) = (slen s)}

findIndex :: (GHC.Types.Char -> GHC.Types.Bool)
          -> s:Data.Text.Fusion.Internal.Stream Char
          -> (Data.Maybe.Maybe {v:Nat | v < (slen s)})

mapAccumL :: (a -> GHC.Types.Char -> (a,GHC.Types.Char))
          -> a
          -> s:Data.Text.Fusion.Internal.Stream Char
          -> (a, {v:Data.Text.Internal.Text | (tlength v) = (slen s)})


length  :: s:Data.Text.Fusion.Internal.Stream Char
        -> {v:GHC.Types.Int | v = (slen s)}
reverse :: s:Data.Text.Fusion.Internal.Stream Char
        -> {v:Data.Text.Internal.Text | (tlength v) = (slen s)}
