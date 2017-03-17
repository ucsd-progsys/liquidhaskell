---
layout: post
title: "Refinement Reflection: Haskell as a theorem prover"
date: 2016-09-18
comments: true
external-url:
author: Niki Vazou
published: true
categories: reflection
demo: RefinementReflection.hs
---

We've taught LiquidHaskell a new trick that we call ``Refinement Reflection''
which lets us turn Haskell into a theorem prover capable of proving arbitrary
properties of code. The key idea is to **reflect** the code of the function into
its **output type**, which lets us then reason about the function at the
(refinement) type level. Lets see how to use refinement types to express a
theorem, for example that fibonacci is a monotonically increasing function, 
then write plain Haskell code to reify a paper-and-pencil-style proof 
for that theorem, that can be machine checked by LiquidHaskell.

<!-- more -->

<br>
<br>
<br>

<div class="row-fluid">
  <div class="span12 pagination-centered">
  <img src="https://eyesofodysseus.files.wordpress.com/2013/06/full-moon-over-ocean-reflection.jpg"
       alt="Reflection" width="300">
       <br>
       <br>
       <br>
       The beauty of Liquid Reflection.
       <br>
       <br>
       <br>
  </div>
</div>


<div class="hidden">
\begin{code}
{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
module RefinementReflection where
import Language.Haskell.Liquid.ProofCombinators

fib :: Int -> Int
propPlusComm :: Int -> Int -> Proof 
propOnePlueOne :: () -> Proof 
fibTwo :: () -> Proof 
fibCongruence :: Int -> Int -> Proof
fibUp :: Int -> Proof 
fibTwoPretty :: Proof 
fibThree :: () -> Proof 
fMono :: (Int -> Int)
      -> (Int -> Proof)
      -> Int
      -> Int 
      -> Proof 
fibMono :: Int -> Int -> Proof 

\end{code}
</div>

Shallow vs. Deep Specifications
-------------------------------

Up to now, we have been using Liquid Haskell to specify and verify "shallow"
specifications that abstractly describe the behavior of functions.  For example,
below, we specify and verify that `fib`restricted to natural numbers, always
terminates returning a natural number.

\begin{code}
{-@ fib :: i:Nat -> Nat / [i] @-}
fib i | i == 0    = 0 
      | i == 1    = 1 
      | otherwise = fib (i-1) + fib (i-2)
\end{code}

In this post we present how refinement reflection is used to verify 
"deep" specifications that use the exact definition of Haskell functions. 
For example, we will prove that the Haskell `fib` function is increasing.



Propositions
------------

To begin with, we import [ProofCombinators][proofcomb], a (Liquid) Haskell 
library that defines and manipulates logical proofs. 

```haskell
import Language.Haskell.Liquid.ProofCombinators
```

A `Proof` is a data type that carries no run time information

```haskell
type Proof = ()
```

but can be refined with desired logical propositions.
For example, the following type states that `1 + 1 == 2`

\begin{code}
{-@ type OnePlusOne = {v: Proof | 1 + 1 == 2} @-}
\end{code}

Since the `v` and `Proof` are irrelevant, we may as well abbreviate 
the above to 

\begin{code}
{-@ type OnePlusOne' = { 1 + 1 == 2 } @-}
\end{code}


As another example, the following function type declares 
that _for each_ `x` and `y` the plus operator commutes. 

\begin{code}
{-@ type PlusComm = x:Int -> y:Int -> {x + y == y + x} @-} 
\end{code}



Trivial Proofs
--------------

We prove the above theorems using Haskell programs. 
The `ProofCombinators` module defines the `trivial` proof

```haskell
trivial :: Proof 
trivial = ()
```

and the "casting" operator `(***)` that makes proof terms look 
nice:

```haskell
data QED = QED

(***) :: a -> QED -> Proof
_ *** _ = ()
```

Using the underlying SMT's knowledge on linear arithmetic, 
we can trivially prove the above propositions.

\begin{code}
{-@ propOnePlueOne :: _ -> OnePlusOne @-} 
propOnePlueOne _ = trivial *** QED 

{-@ propPlusComm :: PlusComm @-} 
propPlusComm _ _ = trivial *** QED 
\end{code}


We saw how we use SMT's knowledge on linear arithmetic 
to trivially prove arithmetic properties. But how can 
we prove ``deep'' properties on Haskell's functions?


Refinement Reflection 
---------------------

Refinement Reflection allows deep specification and 
verification by reflecting the code implementing a Haskell
function into the function’s output refinement type.

Refinement Reflection proceeds in 3 steps: definition, reflection, and application.
Consider reflecting the definition of `fib` into the logic

\begin{code}
{-@ reflect fib @-}
\end{code}

then the following three reflection steps will occur. 

Step 1: Definition 
------------------

Reflection of the Haskell function `fib` defines in logic 
an _uninterpreted_ function `fib` that satisfies the congruence axiom.

In the logic the function `fib` is defined.

```haskell
fib :: Int -> Int 
```

SMT only knows that `fib` satisfies the congruence axiom.

\begin{code}
{-@ fibCongruence :: i:Nat -> j:Nat -> {i == j => fib i == fib j} @-}
fibCongruence _ _ = trivial *** QED 
\end{code}

Other than congruence, SMT knowns nothing for the function `fib`,
until reflection happens!


Step 2: Reflection
------------------

As a second step, Liquid Haskell connects the Haskell function `fib`
with the homonymous logical function, 
by reflecting the implementation of `fib` in its result type. 


The result type of `fib` is automatically strengthened to the following.

```haskell
fib :: i:Nat -> {v:Nat | v == fib i && v = fibP i }
```

That is, the result satisfies the `fibP` predicate
exactly reflecting the implementation of `fib`.

```haskell
fibP i = if i == 0 then 0 else
         if i == 1 then 1 else
         fin (i-1) + fib (i-2)
```

Step 3: Application 
-------------------

With the reflected refinement type,
each application of `fib` automatically unfolds the definition of `fib` 
once. 
As an example, applying `fib` to `0`, `1`, and `2` allows us to prove that `fib 2 == 1`:

\begin{code}
{-@ fibTwo :: _ -> { fib 2 == 1 } @-}
fibTwo _ = [fib 0, fib 1, fib 2] *** QED
\end{code}

Though valid, the above `fibTwo` proof is not pretty! 


Structuring Proofs 
------------------

To make our proofs look nice, we use combinators from 
the `ProofCombinators` library, which exports a family 
of operators `(*.)` where `*` comes from the theory of 
linear arithmetic and the refinement type of `x *. y` 

+ **requires** that `x *. y` holds and 
+ **ensures** that the returned value is equal to `x`.

For example, `(==.)` and `(<=.)` are predefined in `ProofCombinators` as

```haskell
(==.) :: x:a -> y:{a| x==y} -> {v:a| v==x}
x ==. _ = x

(<=.) :: x:a -> y:{a| x<=y} -> {v:a| v==x}
x <=. _ = x
```

Using these predefined operators, we construct paper and pencil-like proofs 
for the `fib` function.

\begin{code}
{-@ fibTwoPretty :: { fib 2 == 1 } @-}
fibTwoPretty 
  =   fib 2 
  ==. fib 1 + fib 0 
  *** QED
\end{code}



Because operator 
-----------------

To allow the reuse of existing proofs, `ProofCombinators` defines the because 
operator `(∵)`

```haskell
(∵) :: (Proof -> a) -> Proof -> a
f ∵ y = f y
```

For example, `fib 3 == 2` holds because `fib 2 == 1`:

\begin{code}
{-@ fibThree :: _ -> { fib 3 == 2 } @-}
fibThree _ 
  =   fib 3 
  ==. fib 2 + fib 1
  ==. 1     + 1      ∵ fibTwoPretty
  ==. 2 
  *** QED
\end{code}



Proofs by Induction (i.e. Recursion) 
------------------------------------

Next, combining the above operators we specify and prove that 
`fib` is increasing, that is for each natural number `i`, 
`fib i <= fib (i+1)`. 

We specify the theorem as a refinement type for `fubUp`
and use Haskell code to persuade Liquid Haskell that 
the theorem holds. 

\begin{code}
{-@ fibUp :: i:Nat -> {fib i <= fib (i+1)} @-}
fibUp i
  | i == 0
  =   fib 0 <. fib 1
  *** QED

  | i == 1
  =   fib 1 <=. fib 1 + fib 0 <=. fib 2
  *** QED

  | otherwise
  =   fib i
  ==. fib (i-1) + fib (i-2)
  <=. fib i     + fib (i-2) ∵ fibUp (i-1)
  <=. fib i     + fib (i-1) ∵ fibUp (i-2)
  <=. fib (i+1)
  *** QED
\end{code}

The proof proceeds _by induction on_ `i`. 

+ The base cases `i == 0` and `i == 1` are represented 
  as Haskell's case splitting. 

+ The inductive hypothesis is represented by recursive calls 
  on smaller inputs. 

Finally, the SMT solves arithmetic reasoning to conclude the proof.  

Higher Order Theorems
----------------------

Refinement Reflection can be used to express and verify higher order theorems!
For example, `fMono` specifies that each locally increasing function is monotonic! 

\begin{code}
{-@ fMono :: f:(Nat -> Int)
          -> fUp:(z:Nat -> {f z <= f (z+1)})
          -> x:Nat
          -> y:{Nat|x < y}
          -> {f x <= f y} / [y] 
  @-}
fMono f thm x y  
  | x + 1 == y
  = f y ==. f (x + 1)
         >. f x       ∵ thm x
        *** QED

  | x + 1 < y
  = f x
  <.  f (y-1)         ∵ fMono f thm x (y-1)
  <.  f y             ∵ thm (y-1)
  *** QED
\end{code}

Again, the recursive implementation of `fMono` depicts the paper and pencil 
proof of `fMono` by induction on the decreasing argument `/ [y]`. 

Since `fib` is proven to be locally increasing by `fUp`, we use `fMono` 
to prove that `fib` is monotonic. 

\begin{code}
{-@ fibMono :: n:Nat -> m:{Nat | n < m }  -> {fib n <= fib m} @-}
fibMono = fMono fib fibUp
\end{code}


Conclusion
----------

We saw how refinement reflection turns Haskell
into a theorem prover by reflecting the code 
implementing a Haskell function into the 
function’s output refinement type.

Refinement Types are used to express theorems, 
Haskell code is used to prove such theorems
expressing paper pencil proofs, and Liquid Haskell 
verifies the validity of the proofs!

Proving `fib` monotonic is great, but this is Haskell!
Wouldn’t it be nice to prove theorems about inductive data types 
and higher order functions? Like fusions and folds? 
Or program equivalence on run-time optimizations like map-reduce?

Stay tuned!

Even better, if you happen you be in Nara for ICFP'16, 
come to my [CUFP tutorial][cufp16] for more!


[cufp16]: http://cufp.org/2016/t6-niki-vazou-liquid-haskell-intro.html
[proofcomb]:https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/ProofCombinators.hs
