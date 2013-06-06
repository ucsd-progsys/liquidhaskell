---
layout: post
title: "Abstracting Over Refinements"
date: 2013-06-03 16:12
comments: true
external-url:
author: Ranjit Jhala and Niki Vazou 
published: true 
categories: abstract-refinements
demo: absref101.hs
---

We've seen all sorts of interesting invariants that can be expressed with
refinement predicates. For example, whether a divisor is [non-zero][blog-dbz], 
the [dimension][blog-len] of lists, ensuring the safety of 
[vector indices][blog-vec] and reasoning about the [set][blog-set] of values
in containers and verifying their [uniqueness][blog-zip].
In each of these cases, we were working with *specific* refinement predicates
that described whatever property was of interest.

Today, (drumroll please), I want to unveil a brand new feature of
LiquidHaskell, which allows us to *abstract* over specific properties or
invariants, which significantly increases the expressiveness of the 
system, whilst still allowing our friend the SMT solver to carry 
out verification and inference automatically.

<!-- more -->

\begin{code}

module MickeyMouse where

import Language.Haskell.Liquid.Prelude (isEven)
\end{code}

Pin The Specification On the Function 
-------------------------------------

Lets look at some tiny *mickey-mouse* examples to see why we may want
to abstract over refinements in the first place.

Consider the following monomorphic `max` function on `Int` values:

\begin{code}
maxInt     :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 
\end{code}

\begin{code} We could give `maxInt` many, quite different and incomparable refinement types like
maxInt :: {v:Int | v >= 0} -> {v:Int | v >= 0} -> {v:Int | v >= 0}
\end{code}

\begin{code}or
maxInt :: {v:Int | v < 10} -> {v:Int | v < 10} -> {v:Int | v < 10}
\end{code}

\begin{code}or even 
maxInt :: {v:Int | (Even v)} -> {v:Int | (Even v)} -> {v:Int | (Even v)}
\end{code}

All of the above are valid. 

But which one is the *right* type? 

At this point, you might be exasperated for one of two reasons.

First, the type enthusiasts among you may cry out -- "What? Does this funny
refinement type system not have **principal types**?"

No. Or, to be precise, of course not!

Principal typing is a lovely feature that is one of the many 
reasons why Hindley-Milner is such a delightful sweet spot. 
Unfortunately, the moment one wants fancier specifications 
one must tearfully kiss principal typing good bye.

Oh well.

Second, you may very well say, "Yes yes, does it even matter? Just pick
one and get on with it already!"

Unfortunately, it matters quite a bit.

Suppose we had a refined type describing valid RGB values:

\begin{code}
{-@ type RGB = {v: Int | ((0 <= v) && (v < 256)) } @-}
\end{code}

Now, if I wrote a function that selected the larger, that is to say, the
more intense, of two RGB values, I would certainly like to check that it 
produced an RGB value!

\begin{code}
{-@ intenser   :: RGB -> RGB -> RGB @-}
intenser c1 c2 = maxInt c1 c2
\end{code}

Well, guess what. The first type (with `v >= 0`) one would tell us that 
the output was non-negative, losing the upper bound. The second type (with
`v < 10`) would cause LiquidHaskell to bellyache about `maxInt` being 
called with improper arguments -- muttering darkly that an RGB value 
is not necesarily less than `10`. As for the third type ... well, you get the idea.

So alas, the choice of type *does* matter. 

\begin{code} If we were clairvoyant, we would give `maxInt` a type like
maxInt :: RGB -> RGB -> RGB 
\end{code}

but of course, that has its own issues. ("What? I have to write a
*separate* function for picking the larger of two *4* digit numbers?!")

Defining Parametric Invariants 
------------------------------

Lets take a step back from the types, and turn to a spot of handwaving.

What's *really* going on with `maxInt`?

Well, the function returns *one of* its two arguments `x` and `y`. 

This means that if *both* arguments satisfy some property then the output
*must* satisfy that property, *regardless of what that property was!*

To teach LiquidHaskell to understand this notion of "regardless of
property" we introduce the idea of **abstracting over refinements**
or, if you prefer, parameterizing a type over its refinements.

In particular, we type `maxInt` as

\begin{code}
{-@ maxInt :: forall <p :: Int -> Prop>. Int<p> -> Int<p> -> Int<p>@-}
\end{code}

Here, the definition says explicitly: *for any property* `p` that is a
property of `Int`, the function takes two inputs each of which satisfy `p`
and returns an output that satisfies `p`. That is to say, `Int<p>` is 
just an abbreviation for `{v:Int | (p v)}`

**Digression: Whither Decidability?** 
At first glance, it may appear that these abstract `p` have taken us into
the realm of higher-order logics, where we must leave decidable checking
and our faithful SMT companion at that door, and instead roll up our 
sleeves for interactive proofs (not that there's anything wrong with that!) 
Fortunately, that's not the case. We simply encode abstract refinements `p` 
as *uninterpreted function symbols* in the refinement logic. 

\begin{code} Uninterpreted functions are special symbols `p` which satisfy only the *congruence axiom*.
forall X, Y. if (X = Y) then  p(X) = p(Y)
\end{code}

Happily, reasoning with such uninterpreted functions is quite decidable
(thanks to Ackermann, yes, *that* Ackermann) and actually rather efficient.
Thus, via SMT, LiquidHaskell happily verifies that `maxInt` indeed behaves
as advertised: the input types ensure that both `(p x)` and `(p y)` hold 
and hence that the returned value in either branch of `maxInt` satisfies 
the refinement  `{v:Int | p(v)}`, thereby ensuring the output type. 

By the same reasoning, we can define the `maximumInt` operator on lists:

\begin{code}
{-@ maximumInt :: forall <p :: Int -> Prop>. x:[Int <p>] -> Int <p>@-}
maximumInt (x:xs) = foldr maxInt x xs
\end{code}

Using Parametric Invariants
---------------------------

Its only useful to parametrize over invariants if there is some easy way 
to *instantiate* the parameters. 

Concretely, consider the function:

\begin{code}
{-@ maxEvens1 :: xs:[Int] -> {v:Int | (Even v)} @-}
maxEvens1 xs = maximumInt xs''
  where 
    xs'      = [ x | x <- xs, isEven x]
    xs''     = 0 : xs'
\end{code}

\begin{code} where the function `isEven` is from the Language.Haskell.Liquid.Prelude library:
{- isEven :: x:Int -> {v:Bool | (Prop(v) <=> (Even x))} -}
isEven   :: Int -> Bool
isEven x = x `mod` 2 == 0
\end{code}

where the predicate `Even` is defined as

\begin{code}
{-@ predicate Even X = ((X mod 2) = 0) @-}
\end{code}

To verify that `maxEvens1` returns an even number, LiquidHaskell 

1. infers that the list `(0:xs')` has type `[{v:Int | (Even v)}]`, 
   that is, is a list of even numbers.

2. automatically instantiates the *refinement* parameter of 
   `maximumInt` with the concrete refinement `{\v -> (Even v)}` and so

3. concludes that the value returned by `maxEvens1` is indeed `Even`.

Parametric Invariants and Type Classes
--------------------------------------

Ok, lets be honest, the above is clearly quite contrived. After all,
wouldn't you write a *polymorphic* `max` function? And having done so,
we'd just get all the above goodness from old fashioned parametricity.

\begin{code} That is to say, if we just wrote:
max     :: forall a. a -> a -> a 
max x y = if x > y then x else y

maximum :: forall a. [a] -> a
maximum (x:xs) = foldr max x xs
\end{code}

then we could happily *instantiate* the `a` with `{v:Int | v > 0}` or
`{v:Int | (Even v)}` or whatever was needed at the call-site of `max`.
Sigh. Perhaps we are still pining for Hindley-Milner.

\begin{code} Well, if this was an ML perhaps we could but in Haskell, the types would be 
(>)     :: (Ord a) => a -> a -> Bool
max     :: (Ord a) => a -> a -> a
maximum :: (Ord a) => [a] -> a
\end{code}

Our first temptation may be to furtively look over our shoulders, and
convinced no one was watching, just pretend that funny `(Ord a)` business
was not there, and quietly just treat `maximum` as `[a] -> a` and summon
parametricity.

That would be most unwise. We may get away with it with the harmless `Ord` but what of, say, `Num`. 

\begin{code} Clearly a function 
numCrunch :: (Num a) => [a] -> a
\end{code}

is not going to necessarily return one of its inputs as an output. 
Thus, it is laughable to believe that `numCrunch` would, if given 
a list of  of even (or positive, negative, prime, RGB, ...) integers, 
return a even (or positive, negative, prime, RGB, ...) integer, since 
the function might add or subtract or multiply or do other unspeakable
things to the numbers in order to produce the output value.

And yet, typeclasses are everywhere. 

How could we possibly verify that

\begin{code}
{-@ maxEvens2 :: xs:[Int] -> {v:Int | (Even v) } @-}
maxEvens2 xs = maximumPoly xs''
  where 
     xs'     = [ x | x <- xs, isEven x]
     xs''    = 0 : xs'
\end{code}

where the helpers were in the usual `Ord` style?

\begin{code}
maximumPoly :: (Ord a) => [a] -> a
maximumPoly (x:xs) = foldr maxPoly x xs

maxPoly     :: (Ord a) => a -> a -> a 
maxPoly x y = if x <= y then y else x
\end{code}

The answer: abstract refinements.

First, via the same analysis as the monomorphic `Int` case, LiquidHaskell
establishes that

\begin{code}
{-@ maxPoly :: forall <p :: a -> Prop>. 
                 (Ord a) => x:a<p> -> y:a<p> -> a<p> @-}
\end{code}

and hence, that

\begin{code}
{-@ maximumPoly :: forall <p :: a -> Prop>. 
                     (Ord a) => x:[a<p>] -> a<p>     @-}
\end{code}

Second, at the call-site for `maximumPoly` in `maxEvens2` LiquidHaskell 
instantiates the type variable `a` with `Int`, and the abstract refinement
parameter `p` with `{\v -> (Even v)}` after which, the verification proceeds 
as described earlier (for the `Int` case).

And So
------

If you've courageously slogged through to this point then you've learnt
that 

1. Sometimes, choosing the right type can be quite difficult! 

2. But fortunately, with *abstract refinements* we needn't choose, but 
   can write types that are parameterized over the actual concrete 
   invariants or refinements, which

3. Can be instantiated at the call-sites i.e. users of the functions.

We started with some really frivolous examples, but buckle your seatbelt 
and hold on tight, because we're going to see some rather nifty things that
this new technique makes possible, including induction, reasoning about
memoizing functions, and *ordering* and *sorting* data. Stay tuned.

[blog-dbz]:     /blog/2013/01/01/refinement-types-101.lhs/ 
[blog-len]:     /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/ 
[blog-vec]:     /blog/2013/03/04/bounding-vectors.lhs/
[blog-set]:     /blog/2013/03/26/talking/about/sets.lhs/
[blog-zip]:     /blog/2013/05/16/unique-zipper.lhs/
