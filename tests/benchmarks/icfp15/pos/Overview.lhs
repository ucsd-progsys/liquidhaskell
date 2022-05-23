\begin{code}
{-# LANGUAGE FlexibleContexts #-}

module OverView where

import Prelude hiding ((.), filter)
import Language.Haskell.Liquid.Prelude

{-@ LIQUID "--no-termination" @-}
\end{code}


2.2 Bounded Refinements
-----------------------
\begin{code}
{-@ find :: forall <p :: Int -> Bool>.
            {x :: Int <p> |- {v:Int | v == x + 1} <: Int <p> }
            (Int -> Bool) -> (Int<p> -> a) -> Int<p> -> a @-}
find :: (Int -> Bool) -> (Int -> a) -> Int -> a
find q k i | q i       = k i
           | otherwise = find q k (i + 1)
\end{code}


2.3 Bounds for Higher-Order Functions
-------------------------------------

\begin{code}
{-@
(.) :: forall < p :: b -> c -> Bool
              , q :: a -> b -> Bool
              , r :: a -> c -> Bool
              >.
       {x::a, w::b<q x> |- c<p w> <: c<r x>}
       f:(y:b -> c<p y>)
    -> g:(z:a -> b<q z>)
    -> x:a -> c<r x>
@-}
(.) f g x = f (g x)

{-@ plusminus :: n:Nat -> m:Nat -> x:{Nat | x <= m} -> {v:Nat | v = (m - x) + n} @-}
plusminus :: Int -> Int -> Int -> Int
plusminus n m = (n+) . (m-)

{- qualif PLUSMINUS(v:int, x:int, y:int, z:int): (v = (x - y) + z) @-}
{- qualif PLUS     (v:int, x:int, y:int)       : (v = x + y)       @-}
{- qualif MINUS    (v:int, x:int, y:int)       : (v = x - y)       @-}
\end{code}



\begin{code}
{-@ filter :: forall <p :: a -> Bool, w :: a -> Bool -> Bool>.
                  {y :: a, b::{v:Bool<w y> | v}|- {v:a| v == y} <: a<p>}
                  (x:a -> Bool<w x>) -> [a] -> [a<p>]
  @-}

filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x       = x : filter f xs
  | otherwise = filter f xs
filter _ []   = []


{-@ measure isPrime :: Int -> Bool @-}

{-@ isPrimeP :: n:Int -> {v:Bool | v <=> isPrime n} @-}
isPrimeP :: Int -> Bool
isPrimeP = undefined

-- | `positives` works by instantiating:
-- p := \v   -> isPrime v
-- q := \n v -> Bool v <=> isPrime n


{-@ primes :: [Int] -> [{v:Int | isPrime v}] @-}
primes     = filter isPrimeP
\end{code}

\begin{code}
data Vec a = Nil | Cons a (Vec a)


{-@
efoldr :: forall <p :: (Vec a) -> b -> Bool, q :: a -> b -> b -> Bool>.
          {y::a, ys :: Vec a, acc:: b<p ys>, z :: {v:Vec a | v = Cons y ys && llen v = llen ys + 1}|- b<q y acc> <: b<p z>}
         (x:a -> acc:b -> b<q x acc>)
      -> b<p Nil>
      -> xs:(Vec a)
      -> b<p xs>
@-}

efoldr :: (a -> b -> b) -> b -> Vec a -> b
efoldr op b Nil         = b
efoldr op b (Cons x xs) = x `op` efoldr op b xs

-- | We can encode the notion of length as an inductive measure @llen@

{-@ measure llen @-}
llen     :: Vec a -> Int
llen (Nil)       = 0
llen (Cons x xs) = 1 + llen(xs)

-- | Finally, lets write a few /client/ functions that use `efoldr` to
-- operate on the `Vec`s.

-------------------------------------------------------------------------
-- | Clients of `efold` -------------------------------------------------
-------------------------------------------------------------------------

-- | First: lets check that the following indeed computes
--   the length of the list.

{-@ size :: xs:Vec a -> {v: Int | v = llen xs} @-}
size :: Vec a -> Int
size = efoldr (\_ n -> n + 1) 0

-- | Second: Appending two lists using `efoldr`
{-@ app  :: xs: Vec a -> ys: Vec a -> {v: Vec a | llen(v) = llen(xs) + llen(ys) } @-}
app xs ys = efoldr (\z zs -> Cons z zs) ys xs
\end{code}
