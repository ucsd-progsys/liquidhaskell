---
layout: post
title: "Refinement Reflection on ADTs: Lists are Monoids"
date: 2016-10-06
comments: true
external-url:
author: Niki Vazou
published: true
categories: reflection, induction, measures, monoids
demo: MonoidList.hs
---

[Previously][refinement-reflection] we saw how Refinement Reflection
can be used to write and prove **in Haskell** theorems **about Haskell**
functions and have such proofs machine checked.

Today, we will see how Refinement Reflection works on **recursive data types**.

As an example, we will prove that **lists are monoids** (under nil and append).

Lets see how to express

* the (monoid) laws as liquid types,
* the (monoid) proofs as plain haskell functions,

and have LiquidHaskell check that the code indeed
proves the corresponding laws.

<!-- more -->

<br>
<br>
<br>

<div class="row-fluid">
  <div class="span12 pagination-centered">
  <img src="http://www.aaronartprints.org/images/Paintings/4597.jpg"
       alt="Recursion" width="300">
       <br>
       <br>
       <br>
       Recursive Paper and Pencil Proofs.
       "Drawing Hands" by Escher.
       <br>
       <br>
       <br>
  </div>
</div>


<div class="hidden">
\begin{code}
{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
module StructuralInduction where
import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (length)

length :: List a -> Int
leftId :: List a -> Proof
rightId :: List a -> Proof
associativity :: List a -> List a -> List a -> Proof
\end{code}
</div>

Lists
-----

First, lets define the `List a` data type

\begin{code}
data List a = N | C a (List a)
\end{code}

Induction on Lists
------------------

As we will see, *proofs* by structural induction will correspond to
*programs* that perform *recursion* on lists. To keep things legit,
we must verify that those programs are total and terminating.

To that end, lets define a `length` function that
computes the natural number that is the size of a
list.

\begin{code}
{-@ measure length               @-}
{-@ length      :: List a -> Nat @-}
length N        = 0
length (C x xs) = 1 + length xs
\end{code}

We lift `length` in the logic, as a [measure][the-advantage-of-measures].

We can now tell Liquid Haskell that when proving termination
on recursive functions with a list argument `xs`, it should
check whether the `length xs` is decreasing.

\begin{code}
{-@ data List [length] a = N | C {hd :: a, tl :: List a} @-}
\end{code}


Reflecting Lists into the Logic
-------------------------------

To talk about lists in the logic, we use the annotation

\begin{code}
{-@ LIQUID "--exact-data-cons" @-}
\end{code}

which **automatically** derives measures for

* *testing* if a value has a given data constructor, and
* *extracting* the corresponding field's value.

For our example, LH will automatically derive the following
functions in the refinement logic.

\begin{spec}
isN :: L a -> Bool         -- Haskell's null
isC :: L a -> Bool         -- Haskell's not . null

select_C_1 :: L a -> a     -- Haskell's head
select_C_2 :: L a -> L a   -- Haskell's tail
\end{spec}

A programmer *never* sees the above operators; they are internally
used by LH to **reflect** Haskell functions into the refinement logic,
as we shall see shortly.

Defining the Monoid Operators
-----------------------------

A structure is a monoid, when it has two operators:

* the identity element `empty` and
* an associative operator `<>`.

Lets define these two operators for our `List`.

* the identity element is the empty list, and
* the associative operator `<>` is list append.

\begin{code}
{-@ reflect empty @-}
empty  :: List a
empty  = N

{-@ infix   <> @-}
{-@ reflect <> @-}
(<>)           :: List a -> List a -> List a
N        <> ys = ys
(C x xs) <> ys = C x (xs <> ys)
\end{code}

LiquidHaskell automatically checked that the recursive `(<>)` 
is terminating, by checking that the `length` of its first
argument is decreasing. Since both the above operators are 
provably terminating, LH lets us reflect them into logic.

As with our [previous][refinement-reflection]
`fibonacci` example, reflection of a function
into logic, means strengthening the result type
of the function with its implementation.

Thus, the **automatically** derived, strengthened
types for `empty` and `(<>)` will be

\begin{spec}
empty   :: {v:List a | v == empty && v == N }

(<>) :: xs:List a -> ys:List a
     -> {v:List a | v == xs <> ys &&
                    v == if isN xs then ys else
                         C (select_C_1 xs) (select_C_2 xs <> ys)
        }
\end{spec}

In effect, the derived checker and selector functions are used
to translate Haskell to logic. The above is just to *explain*
how LH reasons about the operators; the programmer never (directly) 
reads or writes the operators `isN` or `select_C_1` etc.

Proving the Monoid Laws
------------------------

Finally, we have set everything up, (actually LiquidHaskell
did most of the work for us) and we are ready to prove the
monoid laws for the `List`.

First we prove left identity of `empty`.

\begin{code}
{-@ leftId  :: x:List a -> { empty <> x == x } @-}
leftId x
   =   empty <> x
   ==. N <> x
   ==. x
   *** QED
\end{code}

This proof was trivial, because left identity is satisfied
by the way we defined `(<>)`.

Next, we prove right identity of `empty`.

\begin{code}
{-@ rightId  :: x:List a -> { x <> empty  == x } @-}
rightId N
   =   N <> empty
   ==. N
   *** QED

rightId (C x xs)
   =   (C x xs) <> empty
   ==. C x (xs <> empty)
   ==. C x xs        ∵ rightId xs
   *** QED
\end{code}

This proof is more tricky, as it requires **structural induction** which is
encoded in LH proofs simply as **recursion**.  LH ensures that the inductive
hypothesis is appropriately applied by checking that the recursive proof is
total and terminating.  In the `rightId` case, for termination, Liquid Haskell
checked that `length xs < length (C x xs)`.

It turns out that we can prove lots of properties about lists using structural 
induction, encoded in Haskell as

* case splitting,
* recursive calls, and
* rewriting,

To see a last example, lets prove the associativity of `(<>)`.

\begin{code}
{-@ associativity :: x:List a -> y:List a -> z:List a
                  -> { x <> (y <> z) == (x <> y) <> z } @-}
associativity N y z
  =   N <> (y <> z)
  ==. y <> z
  ==. (N <> y) <> z
  *** QED

associativity (C x xs) y z
  =  (C x xs) <> (y <> z)
  ==. C x (xs <> (y <> z))
  ==. C x ((xs <> y) <> z) ∵ associativity xs y z
  ==. (C x (xs <> y)) <> z
  ==. ((C x xs) <> y) <> z
  *** QED
\end{code}

The above proof of associativity reifies the paper and pencil 
proof by structural induction.

With that, we can safely conclude that our user defined list
is a monoid!


Conclusion
----------

We saw how Refinement Reflection can be used to

- specify properties of `ADTs`,
- naturally encode structural inductive proofs of these properties, and
- have these proofs machine checked by Liquid Haskell.

Why is this useful? Because the theorems we prove refer to your Haskell
functions!  Thus you (or in the future, the compiler) can use properties like
monoid or monad laws to optimize your Haskell code.  In the future, we will
present examples of code optimizations using monoid laws. Stay tuned!


[refinement-reflection]: http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2016/09/18/refinement-reflection.lhs/
[the-advantage-of-measures]: http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2014/02/11/the-advantage-of-measures.lhs/
