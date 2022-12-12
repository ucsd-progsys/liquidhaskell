module Fixme where

import GHC.Types

{-@ reflect plus @-}
plus :: Int -> Int -> Int 
plus x y = x + y

{-@ reflect incr @-}
incr :: Int -> Int
incr = plus 1

{-@ relational incr ~ incr :: { x1:Int -> Int 
                              ~ x2:Int -> Int
                              | x1 < x2 :=> r1 x1 < r2 x2 } @-}

-- {-@ relIncrIncr_rtt :: x1:GHC.Types.Int -> x2:{VV : GHC.Types.Int | x1 < x2} -> {VV : () | Fixme.incr x1 < Fixme.incr x2} @-}
-- relIncrIncr_rtt :: GHC.Types.Int -> GHC.Types.Int -> ()
-- relIncrIncr_rtt = () (() () ()) (() () ())

