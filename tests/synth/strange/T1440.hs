{-@ LIQUID "--typed-holes" @-}

module Hole where 

myId :: a -> a 
myId x = _id

incr :: Int -> Int 
{-@ incr :: x:Int -> {v:Int | x < v } @-} 
incr = _incr 

{-@ myMap :: (a -> b) -> xs:[a] -> {v:[b] | len v == len xs} @-}
myMap :: (a -> b) -> [a] -> [b]
myMap = _map
