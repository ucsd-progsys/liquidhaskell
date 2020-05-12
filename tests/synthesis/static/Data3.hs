{-@ LIQUID "--typed-holes" @-}

module Data3 where

import Language.Haskell.Liquid.Synthesize.Error

{-@ data L [length'] a = N | C {x :: a, xs :: (L a)} @-}
data L a = C a (L a) | N

{-@ measure length' @-}
{-@ length' :: L a -> Nat @-}
length' :: L a -> Int 
length' N        = 0
length' (C _ xs) = 1 + length' xs


{-@ appendL :: x: L a -> y: L a -> 
    { v: L a | length' v == length' x + length' y } 
  @-}
appendL N        y = y
appendL (C x xs) y = C x (appendL xs y)

{-@ append :: xs: L a -> ys: L a -> 
    { v: L a | length' v == length' xs + length' ys } 
  @-}
append :: L a -> L a -> L a
append x_S0 x_S1 = appendL x_S0 x_S1
