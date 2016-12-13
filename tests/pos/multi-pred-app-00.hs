module Blank () where

{-@ foo :: forall < p :: Int -> Bool
                  , q :: Int -> Bool >. Int<p,q> -> Int<p> @-}
foo :: Int -> Int
foo x = x
