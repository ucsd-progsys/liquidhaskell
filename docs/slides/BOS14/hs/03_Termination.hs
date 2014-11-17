module Termination where

import Prelude hiding (gcd, mod, map, repeat, take)
import Language.Haskell.Liquid.Prelude

fac   :: Int -> Int
tfac  :: Int -> Int -> Int
map   :: (a -> b) -> List a -> List b
merge :: (Ord a) => List a -> List a -> List a


-------------------------------------------------------------------------
-- | Simple Termination
-------------------------------------------------------------------------

{-@ fac :: Nat -> Nat @-}
fac 0 = 1
fac 1 = 1
fac n = n * fac (n-1)




-------------------------------------------------------------------------
-- | Semantic Termination
-------------------------------------------------------------------------

{-@ gcd :: a:Nat -> b:{v:Nat | v < a} -> Int @-}
gcd :: Int -> Int -> Int
gcd a 0 = a
gcd a b = gcd b (a `mod` b)


{-@ mod :: a:Nat -> b:{v:Nat| 0 < v && v < a} -> {v:Nat | v < b} @-}
mod :: Int -> Int -> Int
mod a b | a - b >  b = mod (a - b) b
        | a - b <  b = a - b
        | a - b == b = 0

-------------------------------------------------------------------------
-- | Explicit Metrics #1 
-------------------------------------------------------------------------

{-@ tfac :: Nat -> n:Nat -> Nat / [n] @-}
tfac acc 0 = acc
tfac acc n = tfac (n * acc) (n-1)




-------------------------------------------------------------------------
-- Explicit Metrics #2 
-------------------------------------------------------------------------

{-@ range :: lo:Nat -> hi:Nat -> [Nat] / [hi-lo] @-}
range :: Int -> Int -> [Int]
range lo hi
  | lo < hi   = lo : range (lo + 1) hi
  | otherwise = []



-------------------------------------------------------------------------
-- | Structural Recursion 
-------------------------------------------------------------------------

data List a = N | C a (List a)

{-@ measure size @-}
size :: List a -> Int 
size (C x xs) = 1 + size xs
size (N)      = 0

{-@ map :: (a -> b) -> xs:List a -> (List b) / [size xs] @-}
map _ N        = N
map f (C x xs) = f x `C` map f xs



-------------------------------------------------------------------------
-- | Default Metrics
-------------------------------------------------------------------------

{-@ data List [size] a = N | C {x :: a, xs :: List a } @-}

map' _ N        = N
map' f (C x xs) = f x `C` map' f xs



-------------------------------------------------------------------------
-- | Termination Expressions Metrics
-------------------------------------------------------------------------

{-@ merge :: xs:_ -> ys:_ -> _ / [size xs + size ys] @-}

merge (C x xs) (C y ys)
  | x < y      = x `C` merge xs (y `C` ys)
  | otherwise  = y `C` merge (x `C` xs) ys
merge _   ys   = ys









-------------------------------------------------------------------------
-- | Infinite Streams
-------------------------------------------------------------------------

{-@ data List [size] a <p :: List a -> Prop>
      = N | C { x  :: a
              , xs :: List <p> a <<p>>
              }
  @-}

{-@ measure cons :: (List a) -> Prop
    cons (C x xs) = true 
    cons (N)      = false 
  @-}

{-@ type Stream a = {xs: List <{\v -> cons v}> a | cons xs} @-}

{-@ Lazy repeat @-}
                 
{-@ repeat :: a -> Stream a @-}
repeat   :: a -> List a
repeat x = x `C` repeat x


{-@ take        :: n:Nat -> Stream a -> {v:List a | size v = n} @-}
take 0 _        = N
take n (C x xs) = x `C` take (n-1) xs
take _ N        = liquidError "never happens"






























-----------------------------------------------------
take            :: Int -> List a -> List a
{-@ invariant {v : List a | 0 <= size v} @-}








