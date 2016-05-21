module Foo where

moo :: Int -> Int
moo n = x + y
  where
    (x, y) = (n, n + 1)
