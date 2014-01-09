module Test0 () where

{-@ type NegInt = {v: Int | v <= 0} @-}
{-@ myabs :: Int -> NegInt @-}
myabs :: Int -> Int
myabs x = if (x > 0) then x else (0 - x)

{-@ type NNList a = {v: [a] | len(v) = 0} @-}
{-@ single :: a -> NNList a @-}
single x = [x] 
