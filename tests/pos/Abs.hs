module Abs () where

absN ::  (Num a, Ord a) => a -> a
absN x = if x > 0 then x else (-x)

absI ::  Int -> Int 
absI x = if x > 0 then x else (-x)

--incI ::  Int -> Int 
--incI = (+) 1

x0 = absN 4
x1 = absI (-5)

--x2 = absI (incI 2)
-- x3 = absI (-3)
