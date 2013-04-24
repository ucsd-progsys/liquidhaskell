module Goo where

{-@ cnt :: Int -> Int @-}
cnt 0 = 0
cnt i = 1 + cnt (i-1)

