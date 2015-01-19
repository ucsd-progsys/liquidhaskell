module Ex1 where

import RIO

{-@ LIQUID "--no-termination" @-}


{-@ measure counter1 :: World -> Int @-}
{-@ measure counter2 :: World -> Int @-}

{-@ incr :: RIO <{\x -> true}, {\w1 x w2 -> x = 5 }> Int @-}
incr :: RIO Int
incr = undefined


{-@ incr' :: RIO <{\x -> true}, {\w1 x w2 -> x = 5}> Int @-}
incr' :: RIO Int
incr' = incr >>= return

{-@ return5 :: x:{v:Int | v = 5} -> RIO <{\y -> true}, {\w1 y w2 -> y = 5}> Int @-}
return5 :: Int -> RIO Int
return5 = undefined









