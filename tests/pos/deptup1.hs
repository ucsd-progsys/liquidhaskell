module Deptup () where

import Language.Haskell.Liquid.Prelude

{-@ data Pair a b <p :: x0:a -> x1:b -> Prop> = P (x :: a) (y :: b<p x>) @-} 
data Pair a b = P a b

incr        :: Int -> Int
incr x      = x + 1

baz x       = P x (incr x)

bazList xs  = map baz xs 

n           = choose 0
xs          = [0..n]

chk (P x y) = liquidAssertB (x < y)
prop_baz    = map chk $ bazList xs 
