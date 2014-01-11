module AnfWierd () where

-- xs :: [Int]
-- xs = let x0 = 0
--          x1 = 1
--          x2 = 2
--          x3 = 3
--          x4 = 4
--          x5 = 5
--          x6 = 6
--          x7 = 7
--          x8 = 8
--          x9 = 9
--      in [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9]

xs :: [Int]
xs = let x0 = 0
         x1 = 1
     in [x0, x1]

ys :: [Int]
ys = [y0, y1]
     where y0 = 0
           y1 = 1

{-@ incr :: x: Int -> {v: Int | v > x} @-}
incr :: Int -> Int
incr y = y + length xs 
  
