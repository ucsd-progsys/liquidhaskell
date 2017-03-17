---
layout: post
title: Proof Reductions on Homomorphisms
date: 2017-01-02
comments: true
external-url:
author: Niki Vazou and Vikraman Choudhury
published: true
categories: reflection, abstract-refinements
demo: Reductions.hs
---

[Previously][refinement-reflection] we saw how Refinement Reflection
can be used to specify and prove theorems about Haskell code.

Today we will see how proof generation can be simplified by 
proof reduction on homomorphic data types. 

As an example, we define a user-defined `Peano` data type
and prove that it enjoys various arithmetic properties 
(like totality of comparison) by 

1. creating a proof that an arithmetic property holds on Natural numbers, and then 
2. reduce the proof from Natural numbers to Peano numbers. 
This proof reduction is possible since Peano numbers are homomorphic to Natural numbers. 

<!-- more -->

<br>
<br>
<br>

<div class="row-fluid">
  <div class="span12 pagination-centered">
  <img src="http://4.bp.blogspot.com/-oltF9WI2KhY/VBMwdj15IvI/AAAAAAAAAtg/V3-k6IylIZM/s1600/picasso_bull.jpg"
       alt="Picasso bull" width="400">
       <br>
       <br>
       <br>
  </div>
</div>


<div class="hidden">
\begin{code}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--totalhaskell"   @-}
{-@ LIQUID "--exactdc"        @-}
{-@ LIQUID "--diffcheck"      @-}
{-@ LIQUID "--pruneunsorted"  @-}
{-@ LIQUID "--eliminate=some" @-}

module Reductions where

import Language.Haskell.Liquid.ProofCombinators

geqZero  :: Peano -> Proof 
leqTotal :: Peano -> Peano -> Proof
toNat    :: Peano -> Int

geqZeroNat          :: Nat -> Proof 
geqZeroByReduction  :: Peano -> Proof 
leqTotalByReduction :: Peano -> Peano -> Proof 
leqTotalNat         :: Nat -> Nat -> Proof

\end{code}

</div>

Properties of Peano Numbers
----------------------------

First, we define `Peano` numbers as a data type 
and the function `leqPeano` that compares two Peano numbers.


\begin{code}
{-@ data Peano [toNat] = Z | S {prev :: Peano } @-}
data Peano = Z | S { prev :: Peano } deriving (Eq)

{-@ reflect leqPeano @-}
leqPeano :: Peano -> Peano -> Bool
leqPeano Z _         = True
leqPeano _ Z         = False
leqPeano (S n) (S m) = leqPeano n m
\end{code}

We can use Refinement Reflection to provide an 
**explicit proof** that no Peano number is greater than zero (`Z`).

\begin{code}
{-@ geqZero :: n:Peano -> {leqPeano Z n} @-}
geqZero n = leqPeano Z n *** QED 
\end{code}

The proof proceeds simply by invocation of the 
first case of the `leqPeano` definition. 

As another Peano property, we can use Refinement Reflection to 
show that comparison on Peano numbers is *total*, 
that is, for every two numbers `n` and `m` 
either `leqPeano n m` or `leqPeano m n` always holds. 

\begin{code}
{-@ leqTotal :: n:Peano -> m:Peano 
             -> {(leqPeano n m) || (leqPeano m n)} 
             /  [toNat n + toNat m] @-}
leqTotal Z m = leqPeano Z m *** QED
leqTotal n Z = leqPeano Z n *** QED
leqTotal (S n) (S m)
  =   (leqPeano (S n) (S m) || leqPeano (S m) (S n))
  ==. (leqPeano n m || leqPeano (S m) (S n)) 
      ? (leqTotal n m)
  ==. (leqPeano n m || leqPeano m n) 
      ? (leqTotal m n)
  *** QED
\end{code}

The proof proceeds by induction on the sum of `n` and `m`. 
Liquid Haskell captures this generalized induction by 
ensuring that the value `toNat n + toNat m` is decreasing
where `toNat` maps Peano to Natural numbers. 

\begin{code}
{-@ measure toNat @-}
{-@ toNat :: Peano -> Nat @-}
toNat Z     = 0
toNat (S n) = 1 + toNat n
\end{code}

Note, that the type `Nat` is just a refinement on the Haskell's integers
\begin{code}
{-@ type Nat = { n:Int | 0 <= n } @-}
type Nat     = Int
\end{code}

Following the totality proof, 
one can prove further properties of Peano comparisons, 
like reflexivity and transitivity.

The above totality proof is verbose! 
Moreover, it is very similar 
to the classic totality on Natural numbers. 
Since the SMT knowns that comparison of Nat is total, we can just reduce 
Peano to Natural number totality!


Reduction of Operators 
-----------------------

Since `toNat` is a homomorphism (i.e., a transformation) from `Peano` to `Nat`
one can compare two Peano numbers via comparison of Natural numbers. 

\begin{code}
{-@ reflect leqPeanoNat @-}
leqPeanoNat :: Peano -> Peano -> Bool 
leqPeanoNat n m = toNat n `leqInt` toNat m  
\end{code}

where `leqInt` the Haskell comparison operator restricted to `Ints`.

\begin{code}
{-@ reflect leqInt @-}
leqInt :: Int -> Int -> Bool 
leqInt x y = x <= y
\end{code}

Note that `leqPeanoNat` is exactly equivalent to `leqPeano`. 
For this blog post, we leave the equivalence proof as an exercise for the reader.


Proof Reductions
-----------------

After reducing the Peano comparison operator to
comparison on Natural numbers, we can reduce 
proofs on Peano numbers to proofs on Natural numbers.
The great benefit of this reduction is that proofs on Natural number
are automated by the underlying SMT solver!

For example, we prove that no Natural number is less than `0`
by unfolding `leqInt` on `0` 
and then let linear arithmetic decision procedure of the SMT complete the proof. 
\begin{code}
{-@ geqZeroNat :: n:Nat -> {leqInt 0 n} @-}
geqZeroNat n = leqInt 0 n *** QED 
\end{code}


We then reduce the above property to the respective property on Peano numbers.
\begin{code}
{-@ geqZeroByReduction :: n:Peano -> {leqPeanoNat Z n} @-}
geqZeroByReduction n 
  = leqPeanoNat Z n ==. True 
  ? reduction toNat geqZeroNat n 
  *** QED 
\end{code}

The reduction occurs via the function `reduction`.
The function `reduction f thm n`, for each homomorphism `f :: a -> b`, 
reduces a theorem `thm x` on `a`s to the respective theorems on `b` via 
[Abstract Refinements][abstract-refinements].
\begin{code}
{-@ reduction :: forall<p :: a -> Proof -> Bool>. 
                 f:(b -> a) 
              -> (x:a -> Proof<p x>) 
              -> (y:b -> Proof<p (f y)>) @-}
reduction :: (b -> a) -> (a -> Proof) -> (b -> Proof)
reduction f thm y = thm (f y)              
\end{code}

Users with model theoretic background may observe that `reduction` 
is actually encoding [Łoś–Tarski preservation theorem][preservation-theorem]!

Similarly, `reduction2` reduces theorems with two `a` arguments
to theorems with two `b` arguments via a homomorphism. 

\begin{code}
{-@ reduction2 :: forall<p :: a -> a -> Proof -> Bool >. 
                  f:(b -> a) 
               -> (x1:a -> x2:a -> Proof<p x1 x2>) 
               -> (y1:b -> y2:b-> Proof<p (f y1) (f y2)>) @-}
reduction2 :: (b -> a) -> (a -> a -> Proof) -> (b -> b -> Proof)
reduction2 f thm y1 y2  = thm (f y1) (f y2)
\end{code}

For example, the SMT-automated proof of totality on Natural numbers 
\begin{code}
{-@ leqTotalNat :: n:Nat -> m:Nat -> { leqInt n m || leqInt m n } @-}
leqTotalNat n m = (leqInt n m || leqInt m n) *** QED 
\end{code}

can be easily reduced to totality on Peano numbers

\begin{code}
{-@ leqTotalByReduction :: n:Peano -> m:Peano
   -> { leqPeanoNat n m || leqPeanoNat m n } @-}
leqTotalByReduction n m 
  = (leqPeanoNat n m || leqPeanoNat m n) ==. True 
  ? reduction2 toNat leqTotalNat n m  
  *** QED 
\end{code}


Conclusion
-----------

We presented an example of how the SMT-automated proofs on 
Natural numbers can be reduced to the respective proofs on the 
Peano numbers, because Peano are homomorphic to Natural numbers. 

Proof reduction greatly simplifies proof composition
as it allows for shorter and more elegant proofs 
that take advantage of SMT-automated or other existing
proofs on homomorphic data structures. 


[refinement-reflection]: http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2016/09/18/refinement-reflection.lhs/
[reduction-lib]: https://github.com/ucsd-progsys/liquidhaskell/tree/develop/include/Language/Haskell/Liquid/Reduction.hs
[abstract-refinements]: http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2013/06/03/abstracting-over-refinements.lhs/
[preservation-theorem]: https://en.wikipedia.org/wiki/%C5%81o%C5%9B%E2%80%93Tarski_preservation_theorem
