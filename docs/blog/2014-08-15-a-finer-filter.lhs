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

<div class="hidden">

\begin{code}

{-@ LIQUID "--short-names" @-}

module Filter (filter) where

import Prelude hiding (filter)
import Data.Set (Set)

import Prelude hiding (filter)
isPos, isEven, isOdd :: Int -> Maybe Int
filter, filter3 :: (a -> Maybe a) -> [a] -> [a]

{-@ measure elts :: [a] -> (Set a) 
    elts ([])   = {v | Set_emp v }
    elts (x:xs) = {v | v = Set_cup (Set_sng x) (elts xs) }
  @-}
 
\end{code}

</div>

Goal
----

What we're after is a way to write a `filter` function such that:

\begin{code} 
{-@ getPoss  :: [Int] -> [Pos] @-}
getPoss      = filter isPos

{-@ getEvens :: [Int] -> [Even] @-}
getEvens     = filter isEven

{-@ getOdds  :: [Int] -> [Odd] @-}
getOdds      = filter isOdd
\end{code}

where `Pos`, `Even` and `Odd` are just subsets of `Int`:

\begin{code}
{-@ type Pos  = {v:Int| 0 < v}        @-}

{-@ type Even = {v:Int| v mod 2 == 0} @-}

{-@ type Odd  = {v:Int| v mod 2 /= 0} @-}
\end{code}

Take 1: Map, maybe?
-------------------

Bowing to the anti-boolean sentiment currently in the air, lets eschew 
the classical approach where the predicates (`isPos` etc.) return `True` 
or `False` and instead implement `filter` using a map.

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
{- isPos          :: Int -> Maybe Pos  @-}
isPos x
  | x > 0          = Just x
  | otherwise      = Nothing

{- isEven         :: Int -> Maybe Even @-}
isEven x
  | x `mod` 2 == 0 = Just x
  | otherwise      = Nothing

{- isOdd          :: Int -> Maybe Odd  @-}
isOdd x
  | x `mod` 2 /= 0 = Just x
  | otherwise      = Nothing
\end{code}

and now, we can achieve our goal!

\begin{code}
{-@ getPoss1 :: [Int] -> [Pos] @-}
getPoss1     = filter1 isPos

{-@ getEvens1 :: [Int] -> [Even] @-}
getEvens1    = filter1 isEven

{-@ getOdds1 :: [Int] -> [Odd] @-}
getOdds1     = filter1 isOdd
\end{code}

**The Subset Guarantee**

Well that was easy! Or was it?

I fear we've *cheated* a little bit.

One of the nice things about the *classical* `filter` is that by eyeballing
the signature:

\begin{spec}
filter :: (a -> Bool) -> [a] -> [a]
\end{spec}

we are guaranteed, via parametricity, that the output list's elements are
a *subset of* the input list's elements. The signature for our new-fangled

\begin{spec}
filter1 :: (a -> Maybe b) -> [a] -> [b]
\end{spec}

yields no such guarantee!

In this case, things work out, because in each case, LiquidHaskell *instantiates*
the type variables `a` and `b` in the signature of `filter1` suitably:

* In `getPoss ` LH instantiates `a := Int` and `b := Pos`
* In `getEvens` LH instantiates `a := Int` and `b := Even`
* In `getOdds ` LH instantiates `a := Int` and `b := Odd`

(Hover over the different instances of `filter1` above to confirm this.)

But in general, we'd rather *not* lose the nice "subset" guarantee that the
classical `filter` provides.


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
{-@ getPoss2 :: [Int] -> [Pos] @-}
getPoss2     = filter2 isPos

{-@ getEvens2 :: [Int] -> [Even] @-}
getEvens2    = filter2 isEven

{-@ getOdds2 :: [Int] -> [Odd] @-}
getOdds2     = filter2 isOdd
\end{code}

Yikes, LH is not impressed -- the red highlight indicates that LH is not
convinced that the functions have the specified types.

Perhaps you know why already?

Since we used **the same** type variable `a` for *both* the 
input *and* output, LH must instantiate `a` with a type that 
matches *both* the input and output, i.e. is a *super-type*
of both, which is simply `Int` in all the cases. 

Consequently, we get the errors above -- "expected `Pos` but got `Int`".

Take 3: Add Abstract Refinement
-------------------------------

What we need is a generic way of specifying that the 
output of the predicate is not just an `a` but an `a` 
that *also* enjoys whatever property we are filtering for. 

This sounds like a job for [abstract refinements][absref] which
let us parameterize a signature over its refinements:

\begin{code}
{-@ filter3      :: forall a <p :: a -> Prop>.
                      (a -> Maybe a<p>) -> [a] -> [a<p>] @-}
filter3 f []     = []
filter3 f (x:xs) = case f x of
                     Just x'  -> x' : filter3 f xs 
                     Nothing ->       filter3 f xs
\end{code}

 Now, we've **decoupled** the filter-property from the type variable `a`.

The input still is a mere `a`, but the output is an `a` with bells on,
specifically, which satisfies the (abstract) refinement `p`.

Voila!

\begin{code}
{-@ getPoss3  :: [Int] -> [Pos] @-}
getPoss3      = filter3 isPos

{-@ getEvens3 :: [Int] -> [Even] @-}
getEvens3     = filter3 isEven

{-@ getOdds3  :: [Int] -> [Odd] @-}
getOdds3      = filter3 isOdd
\end{code}

Now, LH happily accepts each of the above.

At each *use* of `filter` LH separately *instantiates* the `a` and
the `p`. In each case, the `a` is just `Int` but the `p` is instantiated as:

+ In `getPoss ` LH instantiates `p := \v -> 0 <= v`
+ In `getEvens` LH instantiates `p := \v -> v mod 2 == 0`
+ In `getOdds ` LH instantiates `p := \v -> v mod 2 /= 0`

That is, in each case, LH instantiates `p` with the refinement that describes
the output type we are looking for.

**Edit:** At this point, I was ready to go to bed, and so happily 
declared victory and turned in. The next morning, [mypetclone](http://www.reddit.com/r/haskell/comments/2dozs5/liquidhaskell_a_finer_filter/cjrrx3y)
graciously pointed out my folly: the signature for `filter3` makes no guarantees
about the subset property. In fact, 

\begin{code}
doubles = filter3 (\x -> Just (x + x)) 
\end{code}

typechecks just fine, while `doubles` clearly violates the subset property. 

Take 4: 
-------

I suppose the moral is that it may be tricky -- for me at least! -- to read more into
a type than what it *actually says*. Fortunately, with refinements, our types can say
quite a lot.

In particular, lets make the subset property explicit, by

1. Requiring the predicate return its input (or nothing), and,
2. Ensuring  the output is indeed a subset of the inputs.

\begin{code}
{-@ filter      :: forall a <p :: a -> Prop>.
                       (x:a -> Maybe {v:a<p> | v = x})
                    -> xs:[a]
                    -> {v:[a<p>] | Set_sub (elts v) (elts xs)} @-}

filter f []     = []
filter f (x:xs) = case f x of
                    Just x'  -> x' : filter f xs 
                    Nothing ->       filter f xs
\end{code}

where `elts` describes the [set of elements in a list][sets].

**Note:** The *implementation* of each of the above `filter` functions are
the same; they only differ in their type *specification*.

Conclusion
----------

And so, using abstract refinements, we've written a `filter` whose signature guarantees:

* The outputs must be a *subset* of the inputs, and
* The outputs indeed satisfy the property being filtered for.

Another thing that I've learnt from this exercise, is that the old 
school `Boolean` approach has its merits. Take a look at the clever 
"latent predicates" technique of [Tobin-Hochstadt and Felleisen][racket]
or this lovely new [paper by Kaki and Jagannathan][catalyst] which
shows how refinements can be further generalized to make Boolean filters fine.

[sets]:   /blog/2013/03/26/talking-about-sets.lhs/ 
[absref]:   /blog/2013/06/03/abstracting-over-refinements.lhs/ 
[racket]:   http://www.ccs.neu.edu/racket/pubs/popl08-thf.pdf
[catalyst]: http://gowthamk.github.io/docs/icfp77-kaki.pdf
