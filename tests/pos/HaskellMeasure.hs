module Measures where

llen :: [a] -> Int
llen [] = 0
llen (x:xs) = 1 + llen xs

{-@ measure llen @-}

{-@ lllen :: xs:[a] -> {v:Int| (llen xs) = v} @-}

lllen :: [a] -> Int	
lllen [] = 0
lllen (x:xs) = 1 + lllen xs
