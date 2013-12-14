module GCD where

import Prelude hiding (gcd, mod)
import Language.Haskell.Liquid.Prelude
{-@ mod :: a:Nat -> b:{v:Nat| ((v < a) && (v > 0))} -> {v:Nat | v < b} @-}
mod :: Int -> Int -> Int
mod a b | a - b >  b = mod (a - b) b
        | a - b <  b = a - b
        | a - b == b = 0

{-@ gcd :: a:Nat -> b:{v:Nat | v < a} -> Int @-}
gcd :: Int -> Int -> Int
gcd a 0 = a
gcd a b = gcd b (a `mod` b)

{-@ gcd' :: a:Nat -> b:Nat -> Nat / [a, b] @-}
gcd' :: Int -> Int -> Int
gcd' a b | a == 0 = b
         | b == 0 = a
         | a == b = a
         | a >  b = gcd' (a - b) b 
         | a <  b = gcd' a (b - a) 
