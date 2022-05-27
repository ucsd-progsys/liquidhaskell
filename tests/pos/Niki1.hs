module Niki1 () where

import Language.Haskell.Liquid.Prelude

{-@ data Pair a b <p :: x0:a -> x1:b -> Bool> = P (px :: a) (py :: b<p px>) @-} 
data Pair a b = P a b

incr :: Int -> Int
incr x = x + 1

baz :: Int -> Pair Int Int
baz x = P x (incr x)

prop :: Bool
prop = chk (baz n)
  where n = choose 100
{-
foo = baz n
 where n = choose 10
-}
chk :: Pair Int Int -> Bool
chk (P x y) = liquidAssertB (x < y)

