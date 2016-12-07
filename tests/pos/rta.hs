module RTA where 

{-@ type Posi a N = {v:a | v > N} @-}

{-@ incr :: Posi Int 0 -> Posi Int 0 @-}
incr :: Int -> Int 
incr x = x + 1
