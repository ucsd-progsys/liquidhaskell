module Termination where

import Prelude hiding (gcd, mod, map, repeat, take)
import Language.Haskell.Liquid.Prelude

fac   :: Int -> Int

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

gcd :: Int -> Int -> Int
gcd a 0 = a
gcd a b = gcd b (a `mod` b)


mod :: Int -> Int -> Int
mod a b | a - b >  b = mod (a - b) b
        | a - b <  b = a - b
        | a - b == b = 0

-------------------------------------------------------------------------
-- | Explicit Metrics #1 
-------------------------------------------------------------------------

tfac       :: Int -> Int -> Int
tfac acc 0 = acc
tfac acc n = tfac (n * acc) (n-1)




-------------------------------------------------------------------------
-- Explicit Metrics #2 
-------------------------------------------------------------------------

range :: Int -> Int -> [Int]
range lo hi
  | lo < hi   = lo : range (lo + 1) hi
  | otherwise = []



-------------------------------------------------------------------------
-- | Structural Recursion 
-------------------------------------------------------------------------

data List a = N | C a (List a)

{-@ measure size @-}
size          :: List a -> Int 
size (C x xs) = 1 + size xs
size (N)      = 0


map            :: (a -> b) -> List a -> List b
map _ N        = N
map f (C x xs) = f x `C` map f xs



-------------------------------------------------------------------------
-- | Default Metrics
-------------------------------------------------------------------------

map'            :: (a -> b) -> List a -> List b
map' _ N        = N
map' f (C x xs) = f x `C` map' f xs






-------------------------------------------------------------------------
-- | Termination Expressions Metrics
-------------------------------------------------------------------------

merge          :: (Ord a) => List a -> List a -> List a

merge (C x xs) (C y ys)
  | x < y      = x `C` merge xs (y `C` ys)
  | otherwise  = y `C` merge (x `C` xs) ys
merge _   ys   = ys

































--------------------------------------------------------------------------------
-- | CHEAT AREA ----------------------------------------------------------------
--------------------------------------------------------------------------------

-- # START ERRORS 8
-- # END ERRORS   0

{- gcd   :: a:Nat -> b:{v:Nat | v < a} -> Int @-}
{- mod   :: a:Nat -> b:{v:Nat| 0 < v && v < a} -> {v:Nat | v < b} @-}
{- tfac  :: Nat -> n:Nat -> Nat / [n] @-}
{- range :: lo:Nat -> hi:Nat -> [Nat] / [hi-lo] @-}
{- map   :: (a -> b) -> xs:List a -> (List b) / [size xs] @-}
{- merge :: xs:_ -> ys:_ -> _ / [size xs + size ys] @-}
{- data List [size] a = N | C {x :: a, xs :: List a } @-}




























--------------------------------------------------------------------------------
-- | BOILERPLATE ---------------------------------------------------------------
--------------------------------------------------------------------------------
                 
{-@ invariant {v : List a | 0 <= size v} @-}

