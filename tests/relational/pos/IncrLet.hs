module Fixme where

{-@ reflect incr @-}
incr :: Int -> Int
incr = (+ 1)

{-@ relational incr ~ incr :: { x1:Int -> Int 
                              ~ x2:Int -> Int
                              | x1 < x2 :=> r1 x1 < r2 x2 } @-}

{-@ relIncrIncr_rg9 :: x1:GHC.Types.Int 
                    -> x2:{VV : GHC.Types.Int | x1 < x2} 
                    -> {VV : () | incr x1 < incr x2} @-}
relIncrIncr_rg9 :: Int -> Int-> ()
relIncrIncr_rg9 _ _ = ()