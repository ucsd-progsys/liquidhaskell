module DeptupW () where

import Language.Haskell.Liquid.Prelude

{-@ data Pair a b <p :: x0:a -> x1:b -> Bool> = P {pX :: a, pY :: b<p pX> } @-}
data Pair a b = P a b

-- Names are shifty. I bet this would not work with alpha-renaming.
{-@ mkP :: forall a <poo :: xx0:a -> xx1:a -> Bool>. zx: a -> zy: a<poo zx> -> Pair <poo> a a @-}
mkP :: a -> a -> Pair a a
mkP x y = undefined 
