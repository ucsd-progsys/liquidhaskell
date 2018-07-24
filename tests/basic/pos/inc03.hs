module Inc03 where 

{-@ type NN = {v:Int | 0 <= v} @-}

{-@ inc :: NN -> NN @-} 
inc :: Int -> Int 
inc x = x + 1 
