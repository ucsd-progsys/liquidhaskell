{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--maxparams=5"     @-}


{-@ measure ack :: Int -> Int -> Int  @-}

{-@ bar :: n:Int -> x:Int -> f:{(Int -> Int) | f == ack n} -> {v:Bool | f x == ack n x  } @-}
bar :: Int -> Int -> (Int -> Int ) -> Bool 
bar _ _ _ = True