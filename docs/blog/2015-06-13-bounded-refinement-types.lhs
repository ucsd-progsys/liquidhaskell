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

Reusable Specifications
-----------------------

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
{-@ type Neg  = {v:Int | 0 > v} @-}
\end{code}

**Here's the problem:** how can *specify* the behavior of `maximum`
in a way that lets us verify that:

\begin{code}
{-@ posMax :: [Int] -> Pos @-}
posMax xs = maximum [x | x <- xs, x > 0]

{-@ negMax :: [Int] -> Neg @-}
negMax xs = maximum [x | x <- xs, x < 0]
\end{code}

In the first case, the output of `maximum` must be
a `Pos` because *every* input was a `Pos`. Thus, we
might try to type:

\begin{spec}
maximum :: [Pos] -> Pos
\end{spec}

But this specification will not let us verify `negMax`.
Thus, we have a problem: how can we write a precise
specification for `maximum` that we can *reuse* at
different call-sites. Further, how can we do so
enumerating *a priori* the possible contexts (e.g.
`Pos` and `Neg` lists) in which the function may
be used?

Abstracting Refinements
-----------------------

The first idea is one we've [seen before][AbstractRefinements].
Notice that `maximum` returns _one of_ the elements in its input
list. Thus, if *every* element of the list satisfies some
refinement `p` then the output value is also guaranteed to
satisfy `p`. We formalize this notion by *abstracting refinements*
over type specifications. That is, we can type `maximum` as:

\begin{code}
{-@ maximum :: forall <p:: Int -> Prop>. [Int<p>] -> Int<p> @-}
\end{code}

Informally, `Int<p>` stands for `{v:Int | p v}`, that is, `Int`s that
satisfy the property `p`. The signature states that for any property
`p` (of `Int`s), if the input is a list of elements satisfying `p` then
the output is an `Int` satisfying `p`. We can coax SMT solvers into
proving the above type by encoding `p v` as an [uninterpreted function](https://en.wikipedia.org/wiki/Uninterpreted_function)
in the refinement logic.

Thus, refinement abstraction is analagous to type abstraction: it lets us
parameterize signatures over *all* refinements (analogously, types) that
may be _passed in_ at the call-site.

Capturing Dependencies between Relations
----------------------------------------

Unfortunately, in the dependent setting, this is not enough.
Consider `incr` which bumps up its input by 1:

\begin{code}
{-@ incr :: x:Int -> {v:Int | v = x + 1} @-}
incr x = x + 1
\end{code}

We can use `incr` to write and check:

\begin{code}
{-@ incr2 :: x:Int -> {v:Int | v = x + 2} @-}
incr2 x = let y = incr x
              z = incr y
          in
              z
\end{code}

LH uses the specification of `incr` to infer that

+ `y :: {v:Int | v = x + 1}`
+ `z :: {v:Int | v = y + 1}`

and hence, that the result `z` equals `x + 2`.

Now, you're probably wondering to yourself: isn't
this what _function composition_ is for? Indeed!
Lets define:

\begin{code}
{-@ compose' :: (b -> c) -> (a -> b) -> a -> c @-}
compose' f g x = f (g x)
\end{code}

Now, we might try:

\begin{code}
{-@ incr2' :: x:Int -> {v:Int | v = x + 2} @-}
incr2' = compose' incr incr
\end{code}

**Problem 1: Cannot Relate Abstracted Types**

LH _rejects_ the above. This might seem counterintuitive but
in fact, its the right thing to do given the specification of
`compose'` -- at this call-site, each of `a`, `b` and `c` are
instantiated with `Int` as we have no way of *relating* the
invariants associated with those types, e.g. that `b` is one
greater than `a` and `c` is one greater than `b`.

**Problem 2: Cannot Reuse Concrete Types**

At the other extreme, we might try to give compose a concrete
signature:

\begin{code}
{-@ compose'' :: (y:Int -> {z:Int | z = y + 1})
              -> (x:Int -> {z:Int | z = x + 1})
              ->  x:Int -> {z:Int | z = x + 2} @-}
compose'' f g x = f (g x)
\end{code}

This time, LH does verify

\begin{code}
{-@ incr2'' :: x:Int -> {v:Int | v = x + 2} @-}
incr2'' = compose'' incr incr
\end{code}

but this is a pyrhhic victory as we can only `compose` the
toy `incr` function (with itself!) and any attempt to use
it elsewhere will throw a type error.

Goal: Relate Refinements But Keep them Abstract
-----------------------------------------------

The above toy example illustrates the _real_ problem: how
can we **relate** the invariants of the type parameters for
`compose` while simultaneously keeping them **abstract** ?

**Can Abstract Refinements Help?**

HEREHEREHERE

Onto abstracting the type of compose we follow the route of [Abstract Refinements][AbstractRefinements].
We make a second attempt to type function composition and give
`compose2` a type that states that
forall abstract refinements `p`, `q` and `r`
if (1) the first functional argument `f` returns a value that satisfies a relation `p` with respect to its argument `y`, and
   (2) the second functional argument `g` returns a value that satisfies a relation `q` with respect to its argument `x`,
then the result function returns a value that satisfies a relation `r` with respect to its argument `x`:

\begin{code}
{-@ compose''' :: forall <p :: b -> c -> Prop,
                          q :: a -> b -> Prop,
                          r :: a -> c -> Prop>.
                   (y:b -> c<p y>)
                -> (x:a -> b<q x>)
                -> x:a -> c<r x>                   @-}
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
