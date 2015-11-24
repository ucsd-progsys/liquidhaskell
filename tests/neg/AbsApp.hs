module Main where

{-@ id2 :: forall <p :: Int -> Prop>. Int<p> -> Int<p> @-}
id2 :: Int -> Int
id2 x = x

{-@ type Neg = Int<{\x -> x < 0}> @-}

{-@ three :: Neg @-}
three = id2 3

