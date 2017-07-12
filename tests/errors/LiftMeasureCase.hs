module Measures where

llen :: [a] -> Int
llen [] = 0
llen (x:xs) = 1 + llen xs

foo x = x

{-@ measure foo @-}

{-@ measure lllen @-}

{-@ lllen :: xs:[a] -> {v:Int| (lllen xs) = v} @-}

lllen :: [a] -> Int	
lllen [] = 0
lllen (x:xs) = 1 + lllen xs
