module Fixme (foo) where

-- isEven 0 = True
-- isEven n = isEven $ n - 1

incr x = (x, x+1)

{-@ foo :: x:Int -> {v:Int | v > x } @-}
foo :: Int -> Int
foo x = y
  where (w, y) = incr x
