module DependentTriples  where

{-@ type INCR3 = (Int, Int, Int)<{\a b -> a < b}, {\a b c -> b < c }>@-}
{-@ type INCR2 = (Int, Int)<{\a b -> a < b}> @-}

{-@ assume incr3 :: INCR3 @-}
incr3 :: (Int, Int, Int)
incr3 = undefined 

{-@ incr2 :: INCR2 @-}
incr2 :: (Int,Int)
incr2 = let x' = case incr3 of (x, y, z) -> x 
            z' = case incr3 of (x, y, z) -> z 
        in (x',z')



{- 
{-@ uincr3 :: INCR3 @-}
uincr3 :: (Int, Int, Int)
uincr3 = let (x, y, z) = incr3 in (x + 1, y + 1, z +1 )
-}

{-
{-@ uincr3' :: INCR3 @-}
uincr3' :: (Int, Int, Int)
uincr3' = 
  let x' = case incr3 of (xx, xy, xz) -> xx 
      z' = case incr3 of (zx, zy, zz) -> zz 
      y' = case incr3 of (yx, yy, yz) -> yy 
  in (x' + 1, y' + 1, z' +1 )



uincr3 = 
  let z = case incr3 of (x, y, z) -> z 
  let y = case incr3 of (x, y, z) -> y 
  let x = case incr3 of (x, y, z) -> x 
  in (x + 1, y + 1, z +1 )

{-@ type INCR3 = (x::Int, y::{Int | x < y}) @-}


uincr3 = 
  let x :: Int           = case incr3 of (x :: Int, y :: {Int | x < y}) -> x 
  let y :: {Int | x < y} = case incr3 of (x, y) -> y :: {Int | x < y}
  let z = case incr3 of (x, y, z) -> z 
  in (x + 1, y + 1, z +1 )
-}

