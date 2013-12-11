module GCD where
import Prelude hiding (gcd, mod)
import Language.Haskell.Liquid.Prelude 

{-@ mod :: n:Nat -> m:{v:Nat| ((v < n) && (v > 0))} -> {v:Nat | v < m} @-}
mod :: Int -> Int -> Int
mod n m | n - m >  m = mod (n - m) m
        | n - m <  m = n - m
        | n - m == m = 0

{-@ gcd :: n:Nat -> m:{v:Nat | v < n} -> Int @-}
gcd :: Int -> Int -> Int
gcd a 0 = a
gcd a b = gcd b (a `mod` b)
