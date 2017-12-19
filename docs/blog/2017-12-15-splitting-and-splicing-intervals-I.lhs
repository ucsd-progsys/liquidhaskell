---
layout: post
title: Splitting and Splicing Intervals (Part 1)
date: 2017-12-15
comments: true
author: Ranjit Jhala
published: true
tags: reflection, abstract-refinements
demo: IntervalSets.hs
---

[Joachim Breitner](https://twitter.com/nomeata?lang=en)
wrote a [cool post][nomeata-intervals] describing a
library for representing sets of integers
as _sorted lists of intervals_, and how
they were able to formally verify the
code by translating it to Coq using
their [nifty new tool][hs-to-coq].

* First, lets just see how plain refinement types
  let us specify the key "goodness" invariant,
  and check it automatically.

* Next, we'll see how LH's new "type-level computation"
  abilities let us specify and check "correctness",
  and even better, understand _why_ the code works.

(Click here to [demo][demo])

<!-- more -->

<div class="row-fluid">
  <div class="span12 pagination-centered">
  <img src="https://ucsd-progsys.github.io/liquidhaskell-blog/static/img/ribbon.png"
       alt="Ribbons" height="150">
  </div>
</div>

<div class="hidden">
\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--no-termination" @-}

module Intervals where

data Interval  = I
  { from :: Int
  , to   :: Int
  } deriving (Show)

\end{code}
</div>

Encoding Sets as Intervals
--------------------------

The key idea underlying the intervals data structure, is that
we can represent sets of integers like:

```haskell
{ 7, 1, 10, 3, 11, 2, 9, 12, 4}
```

by first *ordering* them into a list

```haskell
[ 1, 2, 3, 4, 7, 9, 10, 11, 12 ]
```

and then *partitioning* the list into compact intervals

```haskell
[ (1, 5), (7, 8), (9, 13) ]
```

That is,

1. Each interval `(from, to)` corresponds to the set
   `{from,from+1,...,to-1}`.

2. Ordering ensures there is a canonical representation
   that simplifies interval operations.

Making Illegal Intervals Unrepresentable
----------------------------------------

We require that the list of intervals be
"sorted, non-empty, disjoint and non-adjacent".
Lets follow the slogan of _make-illegal-values-unrepresentable_
to see how we can encode the legality constraints with refinements.

**A Single Interval**

We can ensure that each interval is **non-empty** by
refining the data type for a single interval to specify
that the `to` field must be strictly bigger than the `from`
field:

\begin{code}
{-@ data Interval = I
      { from :: Int
      , to   :: {v: Int | from < v }
      }
  @-}
\end{code}

Now, LH will ensure that we can only construct *legal*,
non-empty `Interval`s

\begin{code}
goodItv = I 10 20
badItv  = I 20 10     -- ILLEGAL: empty interval!
\end{code}

**Many Intervals**

We can represent arbitrary sets as a *list of* `Interval`s:

\begin{code}
data Intervals = Intervals { itvs :: [Interval] }
\end{code}

The plain Haskell type doesn't have enough teeth to
enforce legality, specifically, to ensure *ordering*
and the absence of *overlaps*. Refinements to the rescue!

First, we specify a *lower-bounded* `Interval` as:

\begin{code}
{-@ type LbItv N = {v:Interval | N <= from v} @-}
\end{code}

Intuitively, an `LbItv n` is one that starts (at or) after `n`.

Next, we use the above to define an *ordered list*
of lower-bounded intervals:

\begin{code}
{-@ type OrdItvs N = [LbItv N]<{\vHd vTl -> to vHd <= from vTl}> @-}
\end{code}

The signature above uses an [abstract-refinement][abs-ref]
to capture the legality requirements.

1. An `OrdInterval N` is a list of `Interval` that are
   lower-bounded by `N`, and

2. In each sub-list, the head `Interval` `vHd` *precedes*
   each in the tail `vTl`.

Legal Intervals
---------------

We can now describe legal `Intervals` simply as:

\begin{code}
{-@ data Intervals = Intervals { itvs :: OrdItvs 0 } @-}
\end{code}

LH will now ensure that illegal `Intervals` are not representable.

\begin{code}
goodItvs  = Intervals [I 1 5, I 7 8, I 9 13]  -- LEGAL

badItvs1  = Intervals [I 1 7, I 5 8]          -- ILLEGAL: overlap!
badItvs2  = Intervals [I 1 5, I 9 13, I 7 8]  -- ILLEGAL: disorder!
\end{code}

Do the types _really_ capture the legality requirements?
In the original code, Breitner described goodness as a
recursively defined predicate that takes an additional
_lower bound_ `lb` and returns `True` iff the representation
was legal:

\begin{code}
goodLIs :: Int -> [Interval] -> Bool
goodLIs _ []              = True
goodLIs lb ((I f t) : is) = lb <= f && f < t && goodLIs t is
\end{code}

We can check that our type-based representation is indeed
legit by checking that `goodLIs` returns `True` whenever it
is called with a valid of `OrdItvs`:

\begin{code}
{-@ goodLIs :: lb:Nat -> is:OrdItvs lb -> {v : Bool | v } @-}
\end{code}


Algorithms on Intervals
-----------------------

We represent legality as a type, but is that _good for_?
After all, we could, as seen above, just as well have written a
predicate `goodLIs`? The payoff comes when it comes to _using_
the `Intervals` e.g. to implement various set operations.

For example, here's the code for _intersecting_ two sets,
each represented as intervals. We've made exactly one
change to the function implemented by Breitner: we added
the extra lower-bound parameter `lb` to the recursive `go`
to make clear that the function takes two `OrdItvs lb`
and returns an `OrdItvs lb`.

\begin{code}
intersect :: Intervals -> Intervals -> Intervals
intersect (Intervals is1) (Intervals is2) = Intervals (go 0 is1 is2)
  where
    {-@ go :: lb:Int -> OrdItvs lb -> OrdItvs lb -> OrdItvs lb @-}
    go _ _ [] = []
    go _ [] _ = []
    go lb (i1@(I f1 t1) : is1) (i2@(I f2 t2) : is2)
      -- reorder for symmetry
      | t1 < t2   = go lb (i2:is2) (i1:is1)
      -- disjoint
      | f1 >= t2  = go lb (i1:is1) is2
      -- subset
      | t1 == t2  = I f' t2 : go t2 is1 is2
      -- overlapping
      | f2 < f1   = (I f' t2 : go t2 (I t2 t1 : is1) is2)
      | otherwise = go lb (I f2 t1 : is1) (i2:is2)
      where f'    = max f1 f2
\end{code}

Internal vs External Verification
----------------------------------

By representing legality **internally** as a refinement type,
as opposed to **externally** as predicate (`goodLIs`) we have
exposed enough information about the structure of the values
that LH can _automatically_ chomp through the above code to
guarantee that we haven't messed up the invariants.

To appreciate the payoff, compare to the effort needed
to verify legality using the external representation
used in the [hs-to-coq proof][intersect-good].

The same principle and simplification benefits apply to both the `union`

\begin{code}
union :: Intervals -> Intervals -> Intervals
union (Intervals is1) (Intervals is2) = Intervals (go 0 is1 is2)
  where
    {-@ go :: lb:Int -> OrdItvs lb -> OrdItvs lb -> OrdItvs lb @-}
    go _ is [] = is
    go _ [] is = is
    go lb (i1@(I f1 t1) : is1) (i2@(I f2 t2) : is2)
      -- reorder for symmetry
      | t1 < t2 = go lb (i2:is2) (i1:is1)
      -- disjoint
      | f1 > t2 = i2 : go t2 (i1:is1) is2
      -- overlapping
      | otherwise  = go lb ( (I f' t1) : is1) is2
      where
        f' = min f1 f2
\end{code}

and the `subtract` functions too:

\begin{code}
subtract :: Intervals -> Intervals -> Intervals
subtract (Intervals is1) (Intervals is2) = Intervals (go 0 is1 is2)
  where
    {-@ go :: lb:Int -> OrdItvs lb -> OrdItvs lb -> OrdItvs lb @-}
    go _ is [] = is
    go _ [] _  = []
    go lb (i1@(I f1 t1) : is1) (i2@(I f2 t2) : is2)
      -- i2 past i1
      | t1 <= f2  = (i1 : go t1 is1 (i2:is2))
      -- i1 past i2
      | t2 <= f1  = (go lb (i1:is1) is2)
      -- i1 contained in i2
      | f2 <= f1, t1 <= t2 = go lb is1 (i2:is2)
      -- i2 covers beginning of i1
      | f2 <= f1 = go t2 (I t2 t1 : is1) is2
      -- -- i2 covers end of i1
      | t1 <= t2 = ((I f1 f2) : go f2 is1 (i2:is2))
      -- i2 in the middle of i1
      | otherwise = (I f1 f2 : go f2 (I t2 t1 : is1) is2)
\end{code}


both of which require [non-trivial][union-good] [proofs][subtract-good]
in the _external style_. (Of course, its possible those proofs can be
simplified.)

Summing Up (and Looking Ahead)
------------------------------

I hope the above example illustrates why _"making illegal states"_
unrepresentable is a great principle for engineering code _and_ proofs.

That said, notice that with [hs-to-coq][nomeata-intervals], Breitner
was able to go _far beyond_ the above legality requirement: he was able
to specify and verify the far more important (and difficult) property
that the above is a _correct_ implementation of a Set library.

Is it even _possible_, let alone _easier_ to do that with LH?

[demo]:              http://goto.ucsd.edu:8090/index.html#?demo=IntervalSets.hs
[intersect-good]:    https://github.com/antalsz/hs-to-coq/blob/8f84d61093b7be36190142c795d6cd4496ef5aed/examples/intervals/Proofs.v#L370-L439
[union-good]:        https://github.com/antalsz/hs-to-coq/blob/b7efc7a8dbacca384596fc0caf65e62e87ef2768/examples/intervals/Proofs_Function.v#L319-L382
[subtract-good]:     https://github.com/antalsz/hs-to-coq/blob/8f84d61093b7be36190142c795d6cd4496ef5aed/examples/intervals/Proofs.v#L565-L648
[abs-ref]:           /tags/abstract-refinements.html
[hs-to-coq]:         https://github.com/antalsz/hs-to-coq
[nomeata-intervals]: https://www.joachim-breitner.de/blog/734-Finding_bugs_in_Haskell_code_by_proving_it
