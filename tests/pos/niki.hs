module Niki () where

import Language.Haskell.Liquid.Prelude

{-@ data Pair a b <p :: x0:a -> x1:b -> Prop> = P (x :: a) (y :: b<p x>) @-} 
data Pair a b = P a b

bar = P (0::Int) (1::Int)
foo = chk bar

chk (P x y) = liquidAssertB (x <= y)
