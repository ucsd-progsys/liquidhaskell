module Measures where

llen :: [a] -> Int
llen [] = 0
llen (x:xs) = 1 + llen xs

{-@ measure lllen @-}

{-@ llen, llllen :: xs:[a] -> {v:Int| (lllen xs) = v} @-}

lllen :: [a] -> Int	
{-@ lllen :: [a] -> Int	@-}
lllen [] = 0
lllen (x:xs) = 1 + lllen xs


llllen = lllen