---
layout: post
title: "Bounded Refinement Types"
date: 2015-06-13
comments: true
external-url:
author: Niki Vazou
published: true
categories: bounded-refinements, abstract-refinements, function-composition
demo: BoundedRefinementTypes.hs
---

While refinement types let SMT solvers do a lot of the "boring" analysis,
they are limited to decidable (first order) logics which can prevent us
from writing *modular* and *reusable* specifications for *higher-order*
functions. Next, lets see why modularity is important, and how we can
recover it using a new technique called **Bounded Refinements**.

<!-- more -->

<div class="hidden">
\begin{code}
module BoundedRefinementTypes where
import Prelude hiding ((.), maximum)
import Language.Haskell.Liquid.Prelude

incr  :: Int -> Int
incr2 :: Int -> Int
incr3 :: Int -> Int

compose1 :: (Int -> Int) -> (Int -> Int) -> Int -> Int
compose1 f g x = f (g x)
incr2'     :: Int -> Int
compose2 :: (b -> c) -> (a -> b) -> a -> c
\end{code}
</div>

The Problem: Reusable Specifications
------------------------------------

Let us suppose, for just a moment, that we live in a dystopian future
where parametric polymorphism and typeclasses have been eliminated
from Haskell. Now, consider the function that returns the largest
element of a list:

\begin{code}
maximum         :: [Int] -> Int
maximum [x]    = x
maximum (x:xs) = max x (maximum xs)
  where
    max a b    = if a < b then b else a
\end{code}

Now, suppose we have refinements:

\begin{code}
{-@ type Pos  = {v:Int | 0 < v} @-}
{-@ type Neg  = {v:Int | 0 < v} @-}
\end{code}

Here's the problem: how can *specify* the behavior of `maximum`
in a way that lets us simultaneouly verify that:

\begin{code}
{-@ posMax :: [Int] -> Pos @-}
posMax xs = maximum [x | x <- xs, x > 0]

{-@ negMax :: [Int] -> Neg @-}
negMax xs = maximum [x | x <- xs, x < 0]
\end{code}

HEREHEREHEREHERE

Any suitable specification would have to enumerate the
situations under which `maximum` may be invoked breaking
modularity.

[Abstract Refinements][AbstractRefinements] overcome the
above modularity problems.
The main idea is that we can type `maximum` by observing
that it returns _one of_ the elements in its input list.
Thus, if every element of the list enjoys some refinement `p`
then the output value is also guaranteed to satisfy `p`.

Concretely, we can type the function as:

\begin{code}
{-@ maximum :: forall<p::Int->Prop>. [Int<p>] -> Int<p> @-}
\end{code}

where informally, `Int<p>` stands for `{v:Int | p v}`,
and `p` is an _uninterpreted function_ in the refinement
logic.

The signature states that for any refinement `p` on `Int`,
the input is a list of elements satisfying `p` and returns
as output an integer satisfying `p`.


Can we use Abstract Refinements to specify a precise type for function composition?

Function Composition
--------------------

To start with, consider a function that increases its argument by `1`

\begin{code}
{-@ incr :: x:Int -> {v:Int | v = x + 1} @-}
incr x = x + 1
\end{code}

How do we use `incr` to create a function that increases its argument by `2`?

We can write a function `incr2` that
first computes `z` by increasing the argument `x`,
and then increases `z.

\begin{code}
{-@ incr2 :: x:Int -> {v:Int | v = x + 2} @-}
incr2 x = let z = incr x in incr z
\end{code}

By the type of `incr`,
LiquidHaskell will infer that `z` is equal to `x + 1`,
`z :: {v:Int | v = x + 1} ` and that
the result is equal to `z + 1`.
Thus, it will accept the post-condition encoded in type signature for `incr2`,
that is that `incr2` increases its argument by `2`.

Since we are in the Haskell world, we would like to write `incr2`
using the higher order function composition.
We define the function `compose` that composes its two functional arguments
\begin{code}
compose f g x = f (g x)
\end{code}

We use `compose` to composing `incr` with itself getting `incr2'`, a function that increases its argument by `2`.
\begin{code}
{-@ incr2' :: x:Int -> {v:Int | v = x + 2} @-}
incr2'      = compose1 incr incr
\end{code}

Our goal is to specify a type for compose
that allows verification of the above type for `incr2'`, by
capturing the compositionality of the refinements.

As a first attempt, we give compose a very specific type that states that
if (1) the first  functional argument increases its argument by `1`, and
   (2) the second functional argument increases its argument by `1`,
then the result function increases its argument by `2`:

\begin{code}
{-@ compose1 :: (y:Int -> {z:Int | z = y + 1})
             -> (x:Int -> {z:Int | z = x + 1})
             ->  x:Int -> {z:Int | z = x + 2} @-}
\end{code}

That was easy, with the above type liquidHaskell does verify that `incr2'`
actually increases its argument by `2`.
But, there is a catch:
_The type of `compose1` it too specific_.

If we use `compose1` with any other functional argument,
for example `incr2` that increases its argument by `2`,
liquidHaskell will reasonably mark the call site as unsafe:

\begin{code}
{-@ incr3 :: x:Int -> {v:Int | v = x + 3} @-}
incr3      = compose1 incr incr2
\end{code}


In any real world application, this super specific type of `compose1` is not acceptable.

An Abstract Type for Compose
----------------------------

Onto abstracting the type of compose we follow the route of [Abstract Refinements][AbstractRefinements].
We make a second attempt to type function composition and give
`compose2` a type that states that
forall abstract refinements `p`, `q` and `r`
if (1) the first functional argument `f` returns a value that satisfies a relation `p` with respect to its argument `y`, and
   (2) the second functional argument `g` returns a value that satisfies a relation `q` with respect to its argument `x`,
then the result function returns a value that satisfies a relation `r` with respect to its argument `x`:

\begin{code}
{-@ compose2 :: forall <p :: b -> c -> Prop,
                        q :: a -> b -> Prop,
                        r :: a -> c -> Prop>.
                f:(y:b -> c<p y>)
             -> g:(x:a -> b<q x>)
             ->  x:a -> c<r x>
@-}
\end{code}

With this type for `compose2` liquidHaskell will prove that composing `incr` by itself
gives a function that increased its argument by `2`:

\begin{code}
{-@ incr2'' :: x:Int -> {v:Int | v = x + 2} @-}
incr2''      = compose2 incr incr
\end{code}

To do so, liquidHaskell will employ the Abstract Refinement Types inference and guess
the appropriate instantiations for `p`, `q`, and `r`.
That is, liquidHaskell will infer that `p` and `q` relate two consecutive numbers
`p, q := \x v -> v = x + 1`
while `r` relates two numbers with distance `2`:
`r := \x v -> v = x + 2`.
Thus, at this specific call site the abstract type of `compose2` will be instantiated to
the concrete type we gave to `compose1`.
And, verification of `incr2''` will succeed.


What is the catch now?
In this second attempt we abstracted the type of `compose2` too much!
In fact, LiquidHaskell cannot prove that the body of `compose2` satisfies its type, just because it does not.

\begin{code}
compose2 f g x = let z = g x in f z
\end{code}

By the precondition of `compose2` we know the result refinements of the functional arguments `f` and `g`.
From the type of `g` we know that `z` satisfies `q` on `x`, i.e. `q x z` holds.
Similarly, from the type of `f` we know that `f z` satisfies `q` on `x`, i.e. `q x z` holds.

With these, liquidHaskell needs to prove that the result `f z` satisfies `r` on `x`, i.e., `r x z` holds.
The required property `r x z` is not satisfied for _arbitrary_ abstract refinements `p`, `q` and `r`, but only for ones that satisfy a _chain property_ that states that for all `x`, `y` and `z`, if `q x y` and `p y z` holds, then `r x z` holds:

<br>

`\ x y z -> q x y ==> p y z ==> r x z`

Bound Abstract Refinements by the Chain Property
------------------------------------------------

We made two attempts to type `compose`.
The first one "failed" as our type was unrealistically specific.
The second failed as it was unsoundly general.
In our third and final attempt
we give `compose` a type that is abstracted over three abstract refinements `p`, `q` and `r`.
But, this time the three refinements are not arbitrary:
they are bounded to satisfy the chain property.

We encode the chain property as a boolean Haskell function:

\begin{code}
chain :: (b -> c -> Bool) -> (a -> b -> Bool)
      -> (a -> c -> Bool) ->  a -> b -> c -> Bool
chain p q r = \ x y z -> q x y ==> p y z ==> r x z
\end{code}

Then we use the new liquidHaskell keyword `bound` to lift the
`chain` function into the a logical bound that
can be used to constrain abstract refinements

\begin{code}
{-@ bound chain @-}
\end{code}

The above bound annotation defines the bound `Chain` that is used as a
constraint that relates the abstract refinements `p`, `q` and `r`
in the type signature of `compose`

\begin{code}
{-@
compose :: forall <p :: b -> c -> Prop,
                   q :: a -> b -> Prop,
                   r :: a -> c -> Prop>.
           (Chain b c a p q r)
        => (y:b -> c<p y>)
        -> (z:a -> b<q z>)
        ->  x:a -> c<r x>
@-}
\end{code}

This type of `compose` is both sound and general enough,
as now we can easily prove that composing `incr` with `incr2`
results in a function that increases its argument by `3`.

\begin{code}
{-@ incr2''' :: x:Int -> {v:Int | v = x + 2} @-}
incr2'''      = compose incr incr

{-@ incr3'' :: x:Int -> {v:Int | v = x + 3} @-}
incr3''      = compose incr2'' incr
\end{code}


Conclusion
----------
We saw how bounds in refinement types allow us to specify a
precise and general type for function composition.
Bounds in refinement types are (haskell typeclases-like) constraints
that constraint the abstract refinement variables to specify certain properties.

We note that liquidHaskell desugars bounds to unbounded refinement types,
thus verification is still performed decidably using the power of the SMT solvers.

Moreover, function composition is not the exclusive user of
Bounded Refinement Types.
On the contrary, we used Bounded Refinement Types
to verify a variety of code, from list-filtering to relational databases.

Read more about bounds in our [ICFP'15 paper][icfp15],
and stay tuned!

<div class="hidden">
\begin{code}
\end{code}
</div>


[icfp15]: http://goto.ucsd.edu/~nvazou/icfp15/main.pdf
[AbstractRefinements]: http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2013/06/03/abstracting-over-refinements.lhs
[queue-wiki]: http://en.wikipedia.org/wiki/Queue_%28abstract_data_type%29
