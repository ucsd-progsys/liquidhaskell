module Measures where

llen :: [a] -> Int
llen [] = 0
llen (x:xs) = 1 + llen xs

{-@ measure foo @-}
foo :: a -> a 
foo x = x

{-@ measure lllen @-}

{-@ lllen :: xs:[a] -> {v:Int| (lllen xs) = v} @-}
lllen :: [a] -> Int	
lllen [] = 0
lllen (x:xs) = 1 + lllen xs
