---
layout: post
title: "Refinement Reflection: Haskell as a theorem prover"
date: 2016-09-05
comments: true
external-url:
author: Niki Vazou
published: true
categories: reflection
demo: RefinementReflection.hs
---

Refinement Reflection turns Haskell into a theorem prover by reflecting the code implementing a function into the function’s output refinement type.
In this post we shall see how one can use a refinement type signature to express a theorem, for example that fibonacci is a monotonically increasing function, then use Haskell code to provide a paper and pensil stype proof for that theorem, and finally use Liquid Haskell to check the validity of the proof.   

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
propPlusAccum :: Int -> Int -> Proof 
propOnePlueOne :: () -> Proof 

\end{code}
</div>

Shallow Specifications
----------------------
Up to now, we have been using Liquid Haskell to specify and verify
"shallow" specifications that abstractly describe the behavior of functions. 
For example, bellow, we specify and verify 
that `fib`restricted to natural numbers, 
always terminates returning a natural number.

\begin{code}
{-@ fib :: i:Nat -> Nat / [i] @-}
fib i | i == 0    = 0 
      | i == 1    = 1 
      | otherwise = fib (i-1) + fib (i-2)
\end{code}


In this post we present how refinement reflection is used to verify 
"deep" specifications that use the exact definition of Haskell functions. 
For example, we will prove that the Haskell `fib` function is increasing!



Propositions
------------
To begin with, we import `ProofCombinators`, a (Liquid) Haskell library that defines 
and manipulates logical proofs. 


```haskell
import Language.Haskell.Liquid.ProofCombinators
```

A proof is a data type that curries no run time information

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
{-@ type OnePlusOne' = { 1 + 1 == 2} @-}
\end{code}


As another example, the following function type declares 
that _for each_ `x` and `y` the plus operator commutes. 

\begin{code}
{-@ type PlusAccum = x:Int -> y:Int -> {x + y == y + x} @-} 
\end{code}



Proofs
------
We prove the above theorems using Haskell programs. 
`ProofCombinators` define the `trivial` proof

```haskell
trivial :: Proof 
trivial = ()
```

and the "casting" operator `(***)` that prettifies proof terms.

```haskell
data QED = QED

(***) :: a -> QED -> Proof
_ *** _ = ()
```

Using the underlying SMT's knownledge on linear arithmetic, 
we trivially prove the above propositions.

\begin{code}
{-@ propOnePlueOne :: _ -> OnePlusOne @-} 
propOnePlueOne _ = trivial *** QED 

{-@ propPlusAccum :: PlusAccum @-} 
propPlusAccum _ _ = trivial *** QED 
\end{code}



We saw how we use SMT's knowledge on linear arithmetic 
to trivially prove arithmetic properties. 
But how can we prove ``deep'' properties on Haskell's functions?


Refinement Reflection 
---------------------
Refinement Reflection allows `deep` specification and verification by
reflecting the code implementing a Haskell
function into the function’s output refinement type.

Refinement Reflection procceds in 3 steps: definition, reflection, and application.
Consider reflecting the definition of `fib` into the logic

\begin{code}
{-@ reflect fib @-}
\end{code}

then the following three reflection steps will occur. 

Step 1: Definition 
------------------
Reflection of the Haskell function `fib` defines in logic 
an _uninterpreted_ function `fib` that satisfies the conguence axiom.

In the logic the fucntion `fib` is defined.

```haskell
fib :: Int -> Int 
```

SMT only knows that `fib` satisfies the conguence axiom.

\begin{code}
fibConguence :: Int -> Int -> Proof
{-@ fibConguence :: i:Nat -> j:Nat -> {i == j => fib i == fib j} @-}
fibConguence _ _ = trivial *** QED 
\end{code}

Other than congruence, SMT knowns nothing for the function `fib`,
until reflection happens!


Step 2: Reflection
------------------

As a second step, Liquid Haskell connects the Haskell function `fib`
with the omonymous logical function, 
by reflecting the implementation of `fib` in its result type. 


The result type of `fib` is automatically strengthened to 

```haskell
fib :: i:Nat -> {v:Nat | v == fib i && v = fibP i }
```

That is, the result satisfies the `fibP` predicate
exactly reflecting the implementation of `fib`

```haskell
fibP i = if i == 0 then 0 else
         if i == 1 then 1 else
         fin (i-1) + fib (i-2)
```

Step 3: Application 
-------------------

With the reflected refinemet type,
each application of `fib` automatically unfolds the definition of `fib` 
once. 
As an example, applying `fib` to `0`, `1`, and `2` allows us to prove that `fib 2 == 1`:

\begin{code}
fibTwo :: () -> Proof 
{-@ fibTwo :: _ -> { fib 2 == 1 } @-}
fibTwo _ = [fib 0, fib 1, fib 2] *** QED
\end{code}

Though valid, 
the above `fibTwo` proof is not pretty! 
To prettify our proofs, we use proof combinators 
that come predified in the `ProofCombinators` library.


Structuring Pretty Proofs 
--------------------------
We equip Liquid Haskell with a family of operators `*.`
where `*` comes from the theory of linear arithmetic and 
the refinement type of `*.` requires that `x *. y` holds and then ensures
that the returned value is equal to `x`.

For example, `(==.)` and `(<=.)` are predefined in `ProofCombinators` as

```haskell
(==.) :: x:a -> y:{a| x==y} -> {v:a| v==x}
x ==. _ = x

(<=.) :: x:a -> y:{a| x<=y} -> {v:a| v==x}
x <=. _ = x
```

Using these predefined operators, we can structure paper&pensil-like proofs 
for the `fib` function 

\begin{code}
fibTwoPretty :: () -> Proof 
{-@ fibTwoPretty :: _ -> { fib 2 == 1 } @-}
fibTwoPretty _ 
  =   fib 2 
  ==. fib 1 + fib 0 
  *** QED
\end{code}



Because operator 
-----------------
To allow proofs using existing proofs, `ProofCombinators` defines the because 
operator `(∵)`

```haskell
(∵) :: (Proof -> a) -> Proof -> a
f ∵ y = f y
```

For example, `fib 3 == 2` holds because `fib 2 == 1`:

\begin{code}
fibThree :: () -> Proof 
{-@ fibThree :: _ -> { fib 3 == 2 } @-}
fibThree _ 
  =   fib 3 
  ==. fib 2 + fib 1
  ==. 1     + 1      ∵ fibTwoPretty ()
  ==. 2 
  *** QED
\end{code}



Pensil & Paper Proofs 
----------------------
Next, using all the above operators we specify and prove that 
`fib` is increasing, that is for each natural number `i`, 
`fib i <= fib (i+1)`. 

We specify the theorem as a refinement type for `fubUp`
and use Haskell code to persuade Liquid Haskell that 
the theorem holds. 

\begin{code}
{-@ fibUp :: i:Nat -> {fib i <= fib (i+1)} @-}
fibUp :: Int -> Proof 
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

The proof procceds by induction on `i`. 
The base cases `i == 0` and `i == 1` are represented 
as Haskell's case splitting. 
The inductive hypothesis is represented by recursive calls 
on smaller inputs. 
At the same time, the SMT solves arithmetic reasoning to conclude the proof.  

Higher Order Theorems
----------------------

Refinement Reflection can be used to express and verify higher order theorems!
For example, `fMono` specifies that each locally increasing function is monotonic! 

\begin{code}
{-@ fMono :: f:(Nat -> Int)
          -> fUp:(z:Nat -> {f z <= f (z+1)})
          -> x:Nat
          -> y:{Nat|x < y}
          -> {f x <= f y} / [y] @-}
fMono :: (Int -> Int)
      -> (Int -> Proof)
      -> Int
      -> Int 
      -> Proof 
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

Again, the recursive implementation of `fMono` 
is used to paper&pensil-like prove the theorem 
by induction on the decresing argument `/ [y]`. 


Since `fib` is proven to be locally increasing by `fUp`,  
we use `fMono` to prove that `fib` is monotonic. 

\begin{code}
fibMono :: Int -> Int -> Proof 
{-@ fibMono :: n:Nat -> m:{Nat | n < m }  -> {fib n <= fib m} @-}
fibMono = fMono fib fibUp
\end{code}


Conclusion
----------
We saw how refinement reflection turns your Haskell
into a theorem prover by reflecting the code implementing a Haskell
function into the function’s (output) refinement type.

Refinement Types are used to express theorems 
and Haskell code is used to prove such theorems
expressing paper&pensil like proofs!

Sweet right? 

If you happen you be in Nara for ICFP'16, 
join my [CUFP tutorial][cufp16] for more!


[cufp16]: http://cufp.org/2016/t6-niki-vazou-liquid-haskell-intro.html
