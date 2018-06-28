module Indexing where

{-@ LIQUID "--gdepth=2" @-}

import Prelude hiding ((!!))

{-@ qualif LenGT(v:int, xs:[a]):   (v < len xs) @-}
{-@ qualif LenGTEQ(v:int, xs:[a]): (v <= len xs) @-}

{-@ (!!) :: xs:[a] -> {i:Int | ?? } -> a @-}
(!!) :: [a] -> Int -> a 
(x:_) !!0 = x 
(_:xs)!!i =            xs!!(i- 1)
_     !!_ =  error "Out of Bounds!"







client1 :: Int
client1 =  [1, 2, 3] !! 0 







client2 :: Int
client2 =  [1, 2, 3] !! 3



