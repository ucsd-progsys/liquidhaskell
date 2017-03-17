module Blank () where

{-@ bar :: forall < p :: Int -> Bool, q :: Int -> Bool>. Int<p> -> Int<p, q> @-}
bar :: Int -> Int
bar x = x
