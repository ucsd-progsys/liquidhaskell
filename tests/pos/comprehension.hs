module Comprehension where

{-@ foo :: n:Int -> [{v:Nat | v <= n}] @-}
foo :: Int -> [Int]
foo n = [0 .. n]

{-@ assume GHC.Enum.enumFromTo :: (Enum a) => lo:a -> hi:a -> [{v:a | lo <= v && v <= hi}] @-}
