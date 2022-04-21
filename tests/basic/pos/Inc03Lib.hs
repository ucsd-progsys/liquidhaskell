module Inc03Lib where

{-@ type NN = {v:Int | 0 <= v} @-}

{-@ incr :: NN -> NN @-} 
incr :: Int -> Int 
incr x = x + 1 
