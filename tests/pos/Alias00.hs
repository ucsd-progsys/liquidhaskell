module Alias00 () where

{-@ type PosInt = {v: Int | v >= 0} @-}

{-@ assert myabs :: Int -> PosInt @-}
myabs   :: Int -> Int
myabs x = if (x > 0) then x else (0 - x)

{-@ type NNList a = {v: [a] | len v > 0} @-}

{-@ assert single :: a -> NNList a @-}
single x = [x] 
