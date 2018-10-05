module LocalSpec where

import LocalSpecLib

{-@ bar :: {x:Int | x > 99} -> {v:Int | v > 100 } @-}
bar :: Int -> Int
bar x = foo x
