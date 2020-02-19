{-@ LIQUID "--typed-holes" @-}

module Data where

{-@ err :: { v: Int | false } -> a @-}
err :: Int -> a
err s = undefined

data L a = C a (L a) | N

{-@ measure length' @-}
{-@ length' :: L a -> Nat @-}
length' :: L a -> Int 
length' N        = 0
length' (C _ xs) = 1 + length' xs

{-@ ex :: x: L a -> { v: (L a) | length' v == length' x } @-}
ex :: L a -> L a 
ex = _hole