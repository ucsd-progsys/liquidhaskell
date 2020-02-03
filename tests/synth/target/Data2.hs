{-@ LIQUID "--typed-holes" @-}

module Data2 where

{-@ data L [length'] a = N | C {x :: a, xs :: (L a)} @-}
data L a = C a (L a) | N

{-@ measure length' @-}
{-@ length' :: L a -> Nat @-}
length' :: L a -> Int 
length' N        = 0
length' (C _ xs) = 1 + length' xs

{-@ ex1 :: xs:(L a) -> {v: (L a) | 2 * length' xs ==  length' v} @-}
ex1 :: L a -> L a 
ex1 = _hole

