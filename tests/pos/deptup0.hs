module Niki () where

import Language.Haskell.Liquid.Prelude

{-@ data Pair a b <p :: x0:a -> x1:b -> Prop> = P (x :: a) (y :: b<p x>) @-} 
data Pair a b = P a b

incr x = x + 1

baz x = P x $ incr x 

prop :: Bool
prop = chk $ baz n
  where n = choose 100

chk (P x y) = liquidAssertB (x < y)

