module IcfpDemo where

import Prelude hiding (gcd, map, repeat, take)
import Language.Haskell.Liquid.Prelude


fac :: Int -> Int
fac n = if n <= 1 then 1 else n * fac (n-1)

{-@ gcd :: a:Nat -> {v:Nat | v < a} -> Nat @-}
gcd :: Int -> Int -> Int
gcd a 0 = a
gcd a b = gcd b (a `mod` b)

{-@ tfac :: Nat -> n:Nat -> Nat / [n] @-}
tfac :: Int -> Int -> Int
tfac x n = if n <= 1 then x
                     else tfac (n*x) (n-1)

{-@ range :: lo:Nat -> hi:Nat -> [Nat] / [hi-lo] @-}
range :: Int -> Int -> [Int]
range lo hi
  | lo < hi   = lo : range (lo + 1) hi
  | otherwise = []

{-@ data L [sz] a <p :: L a -> Prop>
      = N | C (x::a) (xs::L <p> a <<p>>)
  @-}
data L a = N | C a (L a)

{-@ measure sz  :: L a -> Int
    sz (C x xs) = 1 + (sz xs)
    sz (N)      = 0
  @-}
{-@ invariant {v:L a | (sz v) >= 0} @-}

{-@ map :: (a -> b) -> xs:L a -> (L b) / [(sz xs)] @-}
map :: (a -> b) -> L a -> L b
map f (C x xs) = f x `C` map f xs
map _ N        = N

{-@ merge :: xs:_ -> ys:_ -> _ / [(sz xs) + (sz ys)] @-}
merge :: Ord a => L a -> L a -> L a
merge (C x xs) (C y ys)
  | x < y     = x `C` merge xs (y `C` ys)
  | otherwise = y `C` merge (x `C` xs) ys

{-@ measure emp  :: L a -> Prop
    emp (N)      = true
    emp (C x xs) = false
  @-}

{-@ type Stream a = {xs: L <{\v -> not (emp v)}> a | not (emp xs)} @-}

{-@ Lazy repeat @-}
{-@ repeat :: a -> Stream a @-}
repeat :: a -> L a
repeat x = x `C` repeat x

{-@ take :: Nat -> Stream a -> L a @-}
take :: Int -> L a -> L a
take 0 _        = N
take n (C x xs) = x `C` take (n-1) xs
take _ N        = liquidError "never happens"
