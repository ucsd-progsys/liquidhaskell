Termination {#termination}
==========================

Dependent != Refinement
-----------------------

<div class="fragment">**Dependent Types**</div>

+ <div class="fragment">*Arbitrary terms* appear inside types</div> 
+ <div class="fragment">Termination ensures well-defined</div>

<br>

<div class="fragment">**Refinement Types**</div>

+ <div class="fragment">*Restricted refinements* appear in types</div>
+ <div class="fragment">Termination *not* required ...</div> 
+ <div class="fragment">... except, alas, with *lazy* evaluation!</div>

Refinements Need Termination
----------------------------

<div class="fragment">
Fortunately, we can ensure termination *using refinements*
</div>


Termination Using Refinements 
-----------------------------

<a href="http://goto.ucsd.edu:8090/index.html#?demo=GCD.hs" target="_blank">Demo:</a>Lets see some simple examples.

\begin{code}
module Termination where

import Prelude hiding (gcd, mod, map)

fibOk  :: Int -> Int
fibBad :: Int -> Int

{-@ fibBad    :: Int -> Int @-}
fibBad 0      = 1
fibBad 1      = 1
fibBad n      = fibBad (n-1) + fibBad (n-2)


{-@ fibOk :: Nat -> Nat @-}
fibOk n 
  | n <= 1    = 1
  | otherwise = fibOk (n-1) + fibOk (n-2)

{-@ mod :: a:Nat -> b:{v:Nat| ((v < a) && (v > 0))} -> {v:Nat | v < b} @-}
mod :: Int -> Int -> Int
mod a b | a - b >  b = mod (a - b) b
        | a - b <  b = a - b
        | a - b == b = 0

{-@ gcd :: a:Nat -> b:{v:Nat | v < a} -> Int @-}
gcd :: Int -> Int -> Int
gcd a 0 = a
gcd a b = gcd b (a `mod` b)

data L1 a = N1 
          | C1 a (L1 a)

map1 f N1          = N1
map1 f (x `C1` xs) = (f x) `C1` (map1 f xs) 


data L2 a = N2 
          | C2 a (L2 a)


{-@ measure len1 :: (L1 a) -> Int @-} 

{-@ measure len2 :: (L2 a) -> Int 
    len2 (N2)      = 0
    len2 (C2 x xs) = 1 + (len2 xs)  @-}

{-@ invariant {v: (L2 a) | 0 <= (len2 v)} @-}

{-@ data L1 [len1] a = N1 | C1 (x :: a) (xs :: L1 a) @-} 


{-@ data L2 [len2] a = N2 | C2 (x :: a) (xs :: L2 a) @-} 

map2 f N2          = N2
map2 f (x `C2` xs) = (f x) `C2` (map2 f xs) 


merge d xs@(x:xs') ys@(y:ys')
 | x < y      = x : merge dx xs' ys 
 | otherwise  = y : merge dy xs ys' 
 where
    dx        = length xs' + length ys
    dy        = length xs  + length ys'

\end{code}
