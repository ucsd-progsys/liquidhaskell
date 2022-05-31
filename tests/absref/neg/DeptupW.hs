{-@ LIQUID "--expect-any-error" @-}
module DeptupW () where

import Language.Haskell.Liquid.Prelude

{-@ data Pair a b <p :: x0:a -> x1:b -> Bool> = P {pX :: a, pY :: b<p pX> } @-}
data Pair a b = P a b


-- Names are shifty. I bet this would not work with alpha-renaming.
{-@ mkP :: forall a <poo :: xx0:a -> xx1:a -> Bool>. zx: a -> zy: a<poo zx> -> Pair <poo> a a @-}
mkP :: a -> a -> Pair a a
mkP x y = error "TBD"

incr :: Int -> Int
incr x = x - 1

baz x = mkP x (incr x)

chk :: Pair Int Int -> Bool
chk (P x y) = liquidAssertB (x < y)

prop = chk $ baz n
  where n = choose 100
