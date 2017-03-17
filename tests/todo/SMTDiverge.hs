module Chunks where

{-@ go :: Nat -> {v:Int | 1 < v} -> () @-}
go :: Int -> Int -> ()
go d n 
  | d <= n    = ()
  | otherwise = go (d `div` n) n 