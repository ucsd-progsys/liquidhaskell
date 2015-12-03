module TwiceM where

{-@ LIQUID "--short-names" @-}

import RIO

{-@ measure counter :: World -> Int @-}

{-@ incr :: RIO <{\x -> counter x >= 0}, {\w1 x w2 -> counter w2 = counter w1 + 1}>  Nat Nat @-}
incr :: RIO Int
incr = undefined

{-@ incr2 :: RIO <{\x -> counter x >= 0}, {\w1 x w2 -> counter w2 = counter w1 + 2}> Nat Nat @-}
incr2 :: RIO Int
incr2 = incr >> incr 