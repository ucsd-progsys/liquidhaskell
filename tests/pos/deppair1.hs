module Niki () where

import Language.Haskell.Liquid.Prelude

incr  :: Int -> Int
incr x = x + 1


-- THIS DOES NOT WORK: baz  :: Int -> (y: Int, {v: Int | v > y}) @-}
-- BUT THIS DOES
{-@ baz  :: Int -> (Int, Int)<{\fld v -> fld < v }> @-}
baz x = (x, incr x)


{-@ goo :: Int -> (Int, Int, Int)<{\x v -> x < v}, {\x y v -> true}> @-}
goo x = (x, y, z)
  where 
    y = incr x
    z = incr y
