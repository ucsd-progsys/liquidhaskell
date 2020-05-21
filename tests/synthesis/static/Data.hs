{-@ LIQUID "--typed-holes" @-}

module Data where

import Language.Haskell.Liquid.Synthesize.Error

data L a = C a (L a) | N

{-@ measure length' @-}
{-@ length' :: L a -> Nat @-}
length' :: L a -> Int 
length' N        = 0
length' (C _ xs) = 1 + length' xs

{-@ ex :: x: L a -> { v: (L a) | length' v == length' x } @-}
ex :: L a -> L a 
ex x_S0 = x_S0