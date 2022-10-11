{-@ LIQUID "--expect-any-error" @-}
module Inc03 where

{-@ type NN = {v:Int | v <= 0 } @-}

{-@ inc :: NN -> NN @-} 
inc :: Int -> Int 
inc x = x + 1 
