module Niki () where

import Language.Haskell.Liquid.Prelude

{-@ data Pair a b <p :: x0:a -> x1:b -> Bool> = P {pX :: a, pY :: b<p pX> } @-}
data Pair a b = P a b

incr x = x + 1

baz x = P x $ incr x

prop :: Bool
prop = chk $ baz n
  where n = choose 100

chk (P x y) = liquidAssertB (x < y)
