module DepTriples where

{-@ type INCR3 = (Int, Int, Int)<{\a b -> a < b}, {\b a c -> b < c }>@-}

{-@ assume incr3 :: INCR3 @-}
incr3 :: (Int, Int, Int)
incr3 = undefined 

{-@ uincr3 :: INCR3 @-}
uincr3 :: (Int, Int, Int)
uincr3 = case incr3 of (x, y, z) -> (x + 1, y + 1, z +1 )
