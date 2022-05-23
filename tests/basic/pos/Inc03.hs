module Inc03 where

import Inc03Lib 

{-@ incr2 :: NN -> NN @-} 
incr2 :: Int -> Int 
incr2 x = incr (incr x)

{-@ incr3 :: NN -> NN @-} 
incr3 :: Int -> Int 
incr3 = incr . incr . incr 
