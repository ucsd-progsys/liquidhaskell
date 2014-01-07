module Blank where

{-@ foo :: forall < p :: Int -> Prop
                  , q :: Int -> Prop >. Int<p,q> -> Int<p> @-}
foo :: Int -> Int
foo x = x
