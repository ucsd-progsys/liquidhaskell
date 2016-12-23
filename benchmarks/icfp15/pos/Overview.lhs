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
{-@ bound upClosed @-}

upClosed :: (Int -> Bool) -> Int -> Int -> Bool
upClosed p x v =
  p x ==> (v == x + 1) ==> p v

{-@ find :: forall <p :: Int -> Bool>.
            (UpClosed p) =>
            (Int -> Bool) -> (Int<p> -> a) -> Int<p> -> a @-}

find :: (Int -> Bool) -> (Int -> a) -> Int -> a
find q k i | q i       = k i
           | otherwise = find q k (i + 1)
\end{code}


2.3 Bounds for Higher-Order Functions
-------------------------------------

\begin{code}
{-@ bound chain @-}
chain :: (b -> c -> Bool) -> (a -> b -> Bool) -> (a -> c -> Bool) -> a -> b -> c -> Bool
chain p q r = \ x y z -> q x y ==> p y z ==> r x z
{-@
(.) :: forall <p :: b -> c -> Bool, q :: a -> b -> Bool, r :: a -> c -> Bool>.
       (Chain b c a p q r) =>
       (y:b -> c<p y>)
    -> (z:a -> b<q z>)
    ->  x:a -> c<r x>
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
witness :: Eq a => (a -> Bool) -> (a -> Bool -> Bool) -> a -> Bool -> a -> Bool
witness p w = \ y b v -> b ==> w y b ==> (v == y) ==> p v

{-@ bound witness @-}
{-@ filter :: forall <p :: a -> Bool, w :: a -> Bool -> Bool>.
                  (Witness a p w) =>
                  (x:a -> Bool<w x>) -> [a] -> [a<p>]
  @-}

filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x       = x : filter f xs
  | otherwise = filter f xs
filter _ []   = []


{-@ measure isPrime :: Int -> Bool @-}
isPrime :: Int -> Bool
{-@ isPrime :: n:Int -> {v:Bool | v <=> isPrime n} @-}
isPrime = undefined

-- | `positives` works by instantiating:
-- p := \v   -> isPrime v
-- q := \n v -> Bool v <=> isPrime n


{-@ primes :: [Int] -> [{v:Int | isPrime v}] @-}
primes     = filter isPrime
\end{code}

\begin{code}
data Vec a = Nil | Cons a (Vec a)

{-@ bound inductive @-}
inductive inv1 step1 =
    \y ys acc z v ->
     (z == Cons y ys) ==>
     (llen z == llen ys + 1) ==>
     step1 y acc v ==>
     inv1 ys acc ==>
     inv1 z v



{-@
efoldr :: forall <inv :: (Vec a) -> b -> Bool, step :: a -> b -> b -> Bool>.
         (Inductive a b inv step)
      => (x:a -> acc:b -> b<step x acc>)
      -> b<inv Nil>
      -> xs:(Vec a)
      -> b<inv xs>
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
