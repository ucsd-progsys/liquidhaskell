module Blank where

{-@ bar :: forall < p :: Int -> Prop
                  , q :: Int -> Prop >. Int<p> -> Int<p, q> @-}
bar :: Int -> Int
bar x = x
