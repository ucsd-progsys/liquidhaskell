{-@ LIQUID "--expect-any-error" @-}
module Inc04Lib where

{-@ type NN = {v:Int | 0 <= v } @-}

{-@ decr :: NN -> NN @-} 
decr :: Int -> Int 
decr x = x - 1 

{-@ incr :: NN -> NN @-} 
incr :: Int -> Int 
incr x = x + 1 

{-@ down :: x:Int -> {v:Int | v = x - 1} @-}
down :: Int -> Int 
down x = x - 1
