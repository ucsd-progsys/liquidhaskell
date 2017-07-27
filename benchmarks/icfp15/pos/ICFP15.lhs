\begin{code}
module ICFP15 where

import Prelude hiding ((.), (++),  filter)

import Language.Haskell.Liquid.Prelude (unsafeError)

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--short-names" @-}

\end{code}

Function Composition: Bringing Everything into Scope!
-----------------------------------------------------

- Definition

\begin{code}
{-@
(.) :: forall <p :: b -> c -> Bool, q :: a -> b -> Bool, r :: a -> c -> Bool>.
       {x::a, w::b<q x> |- c<p w> <: c<r x>}
       (y:b -> c<p y>)
    -> (z:a -> b<q z>)
    ->  x:a -> c<r x>
@-}
(.) f g x = f (g x)
\end{code}

- Usage

\begin{code}
{-@ plusminus :: n:Nat -> m:Nat -> x:{Nat | x <= m} -> {v:Nat | v = (m - x) + n} @-}
plusminus :: Int -> Int -> Int -> Int
plusminus n m = (n+) . (m-)
\end{code}

- Qualifiers

\begin{code}
{- qualif PLUSMINUS(v:int, x:int, y:int, z:int): (v = (x - y) + z) @-}
{- qualif PLUS     (v:int, x:int, y:int)       : (v = x + y)       @-}
{- qualif MINUS    (v:int, x:int, y:int)       : (v = x - y)       @-}
\end{code}


Folding
-------
see `FoldAbs.hs`

Appending Sorted Lists
-----------------------
\begin{code}
{-@ type OList a = [a]<{\x v -> v >= x}> @-}

{-@ (++) :: forall <p :: a -> Bool, q :: a -> Bool, w :: a -> a -> Bool>.
        {x::a<p> |- a<q> <: a<w x>}
        [a<p>]<w> -> [a<q>]<w> -> [a]<w> @-}
(++) []      ys = ys
(++) (x:xs) ys = x:(xs ++ ys)

{-@ qsort :: xs:[a] -> OList a  @-}
qsort []     = []
qsort (x:xs) = (qsort [y | y <- xs, y < x]) ++ (x:(qsort [z | z <- xs, z >= x]))
\end{code}

Relative Complete
-----------------


\begin{code}
main i = app (check i) i
-- Here p of `app` will be instantiated to
-- p := \v -> i <= v

{-@ check :: x:Int -> {y:Int | x <= y} -> () @-}
check :: Int -> Int -> ()
check x y | x < y     = ()
          | otherwise = unsafeError "oups!"
\end{code}


\begin{code}
{-@ app :: forall <p :: Int -> Bool>.
           {x::Int<p> |- {v:Int| v = x + 1} <: Int<p>}
           (Int<p> -> ()) -> x:Int<p> -> () @-}
app :: (Int -> ()) -> Int -> ()
app f x = if cond x then app f (x + 1) else f x

cond :: Int -> Bool
{-@ cond :: Int -> Bool @-}
cond = undefined
\end{code}

- TODO: compare with related paper

Filter
------

\begin{code}
{-@ filter :: forall <p :: a -> Bool, q :: a -> Bool -> Bool>.
                  {y::a, flag::{v:Bool<q y> | v} |- {v:a | v = y} <: a<p>}
                  (x:a -> Bool<q x>) -> [a] -> [a<p>]
  @-}

filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x       = x : filter f xs
  | otherwise = filter f xs
filter _ []   = []


{-@ measure isPrime :: Int -> Bool @-}
isPrimeP :: Int -> Bool
{-@ isPrimeP :: n:Int -> {v:Bool | v <=> isPrime n} @-}
isPrimeP = undefined

-- | `positives` works by instantiating:
-- p := \v   -> isPrime v
-- q := \n v -> Bool v <=> isPrime n


{-@ primes :: [Int] -> [{v:Int | isPrime v}] @-}
primes     = filter isPrimeP
\end{code}


- filter in Katalyst:

('R filter) :
   l -> f: (x -> {v |  v = false => 'R(x) = emp
                    /\ v = true  => 'R(x) = Rid(x)})
-> {v | Rmem (v) = (Rmem 'R)(l)}


Similar in that the result refinement depends on the 'R.
In our types `p` depends on the `q`.

Precondition constraints the relation 'R  and then post condition

Differences
Katalyst talks about ordering and not other theories, like linear arithmetic

Similarities
Bounds can be seen as Abstract Refinement transformers, i.e., higher order Abstract Refinements.
