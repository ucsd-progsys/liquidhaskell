module Deptup0 where

import Language.Haskell.Liquid.Prelude

{-@ data Pair a b <p :: x0:a -> x1:b -> Bool> = P (x :: a) (y :: b<p x>) @-} 
data Pair a b = P a b

{-@ mkP :: forall a <q :: y0:a -> y1:a -> Bool>. x: a -> y: a<q x> -> Pair <q> a a @-}
mkP :: a -> a -> Pair a a
mkP x y = P x y -- error "TBD"

incr :: Int -> Int
incr x = x + 1

baz x = mkP x (incr x)

chk :: Pair Int Int -> Bool
chk (P x y) = liquidAssertB (x < y)

prop = chk $ baz n
  where n = choose 100
