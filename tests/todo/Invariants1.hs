module Foo where

{-@ invariant {v:[Nat] | (sum v) >= 0} @-}

{-@ measure sum :: [Int] -> Int
    sum([]) = 0
    sum(x:xs) = x + (sum xs)
  @-}

{-@ bad :: [Int] -> {v:[Nat] | (sum v) >= 0} @-}
bad :: [Int] -> [Int]
bad x = x

