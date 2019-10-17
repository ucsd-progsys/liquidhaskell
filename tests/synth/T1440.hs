{-@ LIQUID "--typed-holes" @-}

module Hole where 

myid :: a -> a 
myid x = _id

incr :: Int -> Int 
{-@ incr :: x:Int -> {v:Int | x < v } @-} 
incr = _incr 

-- {-@ mymap :: (a -> b) -> xs:[a] -> {v:[b] | len v == len xs} @-}
-- mymap :: (a -> b) -> [a] -> [b]
-- mymap = _map
