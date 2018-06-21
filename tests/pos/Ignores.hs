module Ignores where 

inc :: Int -> Int 
inc x = x - 1 

{-@ inc :: Nat -> Nat @-}

{-@ ignore inc @-}
