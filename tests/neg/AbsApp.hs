-- FAILING TEST: This should be rejected if we wish to disallow applying
-- concrete refinements to non-refined types (e.g. Int) where they are currently
-- silently dropped.
-- issue #519

module Main where

{-@ id2 :: forall <p :: Int -> Prop>. Int<p> -> Int<p> @-}
id2 :: Int -> Int
id2 x = x

{-@ type Neg = Int<{\x -> x < 0}> @-}

{-@ three :: Neg @-}
three = id2 3

