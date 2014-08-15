---
layout: post
title: "A Finer Filter"
date: 2014-08-15 16:12
author: Ranjit Jhala
published: true
comments: true
external-url:
categories: abstract-refinements 
demo: filter.hs
---

This morning, I came across this [nice post](https://twitter.com/ertesx/status/500034598042996736) which describes how one can write a very expressive type for 
`filter` using [singletons](https://hackage.haskell.org/package/singletons).

Lets see how one might achieve this with [abstract refinements][absref].

<!-- more -->

<span class="hidden">

\begin{code}

import Prelude hiding (filter)

import Prelude hiding (filter)
isNat, isEven, isOdd :: Int -> Maybe Int
filter :: (a -> Maybe a) -> [a] -> [a]

{-@ type Even = {v:Int| v mod 2 == 0} @-}
{-@ type Odd  = {v:Int| v mod 2 /= 0} @-}

\end{code}

</span>

Goal
----

What we're after is a way to write a `filter` function such that:

< {-@ getNats :: [Int] -> [Nat] @-}
< getNats     = filter isNat
< 
< {-@ getEvens :: [Int] -> [Even] @-}
< getEvens    = filter isEven
< 
< {-@ getOdds :: [Int] -> [Odd] @-}
< getOdds     = filter isOdd


where `Nat`, `Even` and `Odd` are just subsets of `Int`:

< {-@ type Nat  = {v:Int| 0 <= v}       @-}
< 
< {-@ type Even = {v:Int| v mod 2 == 0} @-}
< 
< {-@ type Odd  = {v:Int| v mod 2 /= 0} @-}


Take 1: `map`, maybe?
---------------------

Bowing to the anti-boolean sentiment currently in the air, lets eschew 
the classical approach where the predicates (`isNat` etc.) return `True` 
or `False` and instead implement `filter` using a `map`.

\begin{code}
filter1          :: (a -> Maybe b) -> [a] -> [b]

filter1 f []     = []
filter1 f (x:xs) = case f x of
                     Just y  -> y : filter1 f xs 
                     Nothing ->     filter1 f xs
\end{code}

To complete the picture, we need just define the predicates as
functions returning a `Maybe`:

\begin{code}
{-@ isNat          :: Int -> Maybe Nat  @-}
isNat x
  | x >= 0         = Just x
  | otherwise      = Nothing

{-@ isEven         :: Int -> Maybe Even @-}
isEven x
  | x `mod` 2 == 0 = Just x
  | otherwise      = Nothing

{-@ isOdd          :: Int -> Maybe Odd  @-}
isOdd x
  | x `mod` 2 /= 0 = Just x
  | otherwise      = Nothing
\end{code}

and now, we can achieve our goal!

\begin{code}
{-@ getNats1 :: [Int] -> [Nat] @-}
getNats1     = filter1 isNat

{-@ getEvens1 :: [Int] -> [Even] @-}
getEvens1    = filter1 isEven

{-@ getOdds1 :: [Int] -> [Odd] @-}
getOdds1     = filter1 isOdd
\end{code}

It all works out, because in each case, LiquidHaskell *instantiates*
the type variables `a` and `b` in the signature of `filter` suitably:

Function       `a`      `b`
------------   ------   -------
`getNats`      `Int`    `Nat`
`getEvens`     `Int`    `Even`
`getOdds`      `Int`    `Odd`

(Hover over the different instances of `filter1` above to confirm this.)

**But but...**

Well that was easy! Or was it?

I fear we've *cheated* a little bit.

One of the nice things about the *classical* `filter` is that by eyeballing
the signature:

< filter :: (a -> Bool) -> [a] -> [a]

we are guaranteed, via parametricity, that the output list's elements are
a *subset of* the input list's elements. The signature for our new-fangled

< filter1 :: (a -> Maybe b) -> [a] -> [b]

yields no such guarantee!


Take 2: One Type Variable
-------------------------

Easy enough! Why do we need *two* type variables anyway?

\begin{code}
filter2          :: (a -> Maybe a) -> [a] -> [a]

filter2 f []     = []
filter2 f (x:xs) = case f x of
                     Just y  -> y : filter2 f xs 
                     Nothing ->     filter2 f xs
\end{code}

There! Now the `f` is forced to take or leave its input `x`, 
and so we can breathe easy knowing that `filter2` returns a 
subset of its inputs.

But...

\begin{code}
{-@ getNats2 :: [Int] -> [Nat] @-}
getNats2     = filter2 isNat

{-@ getEvens2 :: [Int] -> [Even] @-}
getEvens2    = filter2 isEven

{-@ getOdds2 :: [Int] -> [Odd] @-}
getOdds2     = filter2 isOdd
\end{code}

Yikes, LH is not impressed!

Perhaps you know why already?

Since we used **the same** type variable `a` for *both* the 
input *and* output, LH must instantiate `a` with a type that 
matches *both* the input and output, i.e. is a *super-type*
of both, which is simply `Int` in all the cases. 

Consequently, we get the errors above -- "expected Nat but got Int".

Take 3: Add Abstract Refinement
-------------------------------

What we need is a generic way of specifying that the 
output of the predicate is not just an `a` but an `a` that
*also enjoys* whatever property we are filtering for. 

This sounds like a job for [abstract refinements][absref] which
let us parameterize a signature over its refinements:

\begin{code}
{-@ filter :: forall a <p :: a -> Prop>.
                (a -> Maybe a<p>) -> [a] -> [a<p>] @-}
filter f []     = []
filter f (x:xs) = case f x of
                    Just x'  -> x' : filter f xs 
                    Nothing ->       filter f xs
\end{code}

(Note that the *implementation* of each of the `filter` functions are
the same; they only differ in their type *specification*.)

Now, we've **decoupled** the filter-property from the type variable `a`.

The input still is a mere `a`, but the output is an `a` with bells on,
specifically, which satisfies the (abstract) refinement `<p>`, so
everything works out.

Voila!

\begin{code}
{-@ getNats :: [Int] -> [Nat] @-}
getNats     = filter isNat

{-@ getEvens :: [Int] -> [Even] @-}
getEvens    = filter isEven

{-@ getOdds :: [Int] -> [Odd] @-}
getOdds     = filter isOdd
\end{code}

Now, at each *use* of `filter` LH separately instantiates the `a` and
the `p`. In each case, the `a` is just `Int` but the `p` is:

Function       `p`
------------   --------------------
`getNats`      `\v -> 0 <= v`
`getEvens`     `\v -> v mod 2 == 0`
`getOdds`      `\v -> v mod 2 /= 0`


Conclusion
----------

Using abstract refinements, we've written a `filter` whose signature guarantees:

* The outputs are a subset of the inputs, that,
* Indeed satisfy the property being filtered for.

Finally, if you are of the old school, and like your filters `Boolean`, then take
a look at this lovely new [paper by Kaki and Jagannathan](http://gowthamk.github.io/docs/icfp77-kaki.pdf).

[absref]:  /blog/2013/06/03/abstracting-over-refinements.lhs/ 
