module Client521 where

import Lib521 

{-@ bar :: { xs : [a] | size xs > 1 } -> [a] @-}
bar :: [a] -> [a]
bar xs = xs 

{-@ bing :: xs:[a] -> {v:Int | v = size xs} @-}
bing :: [a] -> Int 
bing [] = 0 
bing (x:xs) = 1 + bing xs 
