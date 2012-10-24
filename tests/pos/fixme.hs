module Fib where

{-@ sumn :: (Int, a, b, c, d) -> ({v: Int | v >= 0}, a, b, c, d) @-}
sumn :: (Int, a, b, c, d) -> (Int, a, b, c, d)
sumn (n, x1, x2, x3, x4) 
  | n <= 0    = (0, x1, x2, x3, x4) 
  | otherwise = let (z, y1, y2, y3, y4) = sumn (n-1, x1, x2, x3, x4) 
                in (n + z, y1, y2, y3, y4)





