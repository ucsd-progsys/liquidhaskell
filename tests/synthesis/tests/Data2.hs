{-@ LIQUID "--typed-holes" @-}

module Data2 where

import Language.Haskell.Liquid.Synthesize.Error

{-@ data L [length'] a = N | C {x :: a, xs :: (L a)} @-}
data L a = C a (L a) | N

{-@ measure length' @-}
{-@ length' :: L a -> Nat @-}
length' :: L a -> Int 
length' N        = 0
length' (C _ xs) = 1 + length' xs

{-@ appendL :: x: L a -> y: L a -> { v: L a | length' v == length' x + length' y } @-}
appendL N        y = y
appendL (C x xs) y = C x (appendL xs y)

{-@ ex1 :: xs:(L a) -> {v: (L a) | 2 * length' xs ==  length' v} @-}
ex1 :: L a -> L a 
ex1 = _hole

