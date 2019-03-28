module Hole where 

incr :: Int -> Int 
{-@ incr :: x:Int -> {v:Int | x < v } @-} 
incr = _incr 

{-@ mymap :: (a -> b) -> xs:[a] -> {v:[b] | len v == len xs} @-}
mymap :: (a -> b) -> [a] -> [b]
mymap = _map