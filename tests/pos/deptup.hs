module Deptup0 () where

import Language.Haskell.Liquid.Prelude

{-@ data Pair a b <p :: x0:a -> x1:b -> Prop> = P (x :: a) (y :: b<p x>) @-} 
data Pair a b = P a b


{-- TODO: mkP :: forall a b <p :: a -> b -> Prop>. x: a -> y: b<p x> -> Pair <p> a b  --}

mkP :: a -> a -> Pair a a 
mkP x y = P x y

incr x = x + 1

baz x  = mkP x (incr x)

chk (P x y) = liquidAssertB (x < y)

prop = chk $ baz n
  where n = choose 100

bazList  xs = map baz xs

n           = choose 0

xs          = [0,1,2,3,4]

prop_baz    = map chk $ bazList xs 
