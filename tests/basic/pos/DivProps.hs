module DivProps where

{-@
testDiv
  :: x:Int
  -> {y:Int | y /= 0}
  -> {v:Int |
         ((x >= 0 && y >= 0) => v >= 0) &&
         ((x >= 0 && y >= 1) => v <= x) &&
         ((1 < y && x > 0)  => v < x) &&
         ((1 < y && x < -1)   => v > x) &&
         ((y >= 1 && x >= 0)  => v <= x) &&
         ((x < 0 && y > 0)   => v <= 0) &&
         ((x > 0 && y < 0)   => v <= 0) &&
         ((x < 0 && y < 0)   => v >= 0)
     }
  @-}
testDiv :: Int -> Int -> Int
testDiv x y = div x y


{-@
testQuot
  :: x:Int
  -> y:{v:Int | v /= 0}
  -> {v:Int |
         ((x >= 0 && y >= 0) => v >= 0) &&
         ((x >= 0 && y >= 1) => v <= x)
     }
@-}
testQuot :: Int -> Int -> Int
testQuot x y = quot x y

{-@
testRem
  :: x:Int
  -> y:{v:Int | v /= 0}
  -> {v:Int | 0 <= x && 0 < y => 0 <= v && v < y}
@-}
testRem :: Int -> Int -> Int
testRem x y = rem x y

{-@
testMod
  :: x:Int
  -> y:{v:Int | v /= 0}
  -> {v:Int | 0 <= x && 0 < y => 0 <= v && v < y}
@-}
testMod :: Int -> Int -> Int
testMod x y = mod x y
