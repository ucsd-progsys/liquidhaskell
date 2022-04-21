module Positivity2 where

data Evil a = Very (Evil a -> a)

{-@ type Bot = {v: () | false} @-}

{-@ bad :: Evil Bot -> Bot @-}
bad :: Evil () -> ()
bad (Very f) = f (Very f)

{-@ worse :: Bot @-}
worse :: ()
worse = bad (Very bad)
