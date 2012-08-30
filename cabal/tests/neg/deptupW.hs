module Deptup0 where

import Language.Haskell.Liquid.Prelude

{-@ data Pair a b <p :: x0:a -> x1:b -> Bool> = P (x :: a) (y :: b<p x>) @-} 
data Pair a b = P a b

{-@ mkP :: forall a <p :: x0:a -> x1:a -> Bool>. x: a -> y: a<p x> -> Pair <p> a a @-}
mkP :: a -> a -> Pair a a
mkP x y = error "TBD"

incr :: Int -> Int
incr x = x - 1

baz x = mkP x (incr x)

chk :: Pair Int Int -> Bool
chk (P x y) = liquidAssertB (x < y)

prop = chk $ baz n
  where n = choose 100
