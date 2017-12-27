---
layout: post
title: Splitting and Splicing Intervals (Part 2)
date: 2017-12-24
comments: true
author: Ranjit Jhala
published: true
tags: reflection, abstract-refinements
demo: RangeSet.hs
---

[Previously][splicing-1], we saw how the principle of
_"making illegal states unrepresentable"_ allowed LH
to easily enforce a _key invariant_ in
[Joachim](https://twitter.com/nomeata?lang=en)
Breitner's library for representing sets of integers
as [sorted lists of intervals][nomeata-intervals].

However, with [hs-to-coq][hs-to-coq], Breitner
was able to do much more: Coq let him specify and
verify that his code properly implemented a Set library.

Today, lets see how LH's new _"type-level computation"_
abilities let us reason about intervals, while using the
SMT solver to greatly simplify the overhead of proof.

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
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--ple"            @-}

module RangeSet where

import           Prelude hiding (min, max)
import           Language.Haskell.Liquid.NewProofCombinators
\end{code}
</div>


Intervals
---------

Recall that the key idea is to represent sets of integers like

```haskell
{ 7, 1, 10, 3, 11, 2, 9, 12, 4}
```

as ordered lists of *intervals*

```haskell
[ (1, 5), (7, 8), (9, 13) ]
```

where each pair `(i, j)` represents the set `{i, i+1,..., j-1}`.

To verify that the implementation correctly implements a set
data type, we need a way to

1. _Specify_ the set of values being described,
2. _Establish_ some key properties of these sets.

Range-Sets: Semantics of Intervals
----------------------------------

We can describe the set of values corresponding
to (i.e. ``the semantics of'') an interval `i, j`
by importing the `Data.Set` library

\begin{code}
import qualified Data.Set as S
\end{code}

and then using the library to write a function
`rng i j` that defines the **range-set** `{i..j-1}`

\begin{code}
{-@ reflect rng @-}
{-@ rng :: i:Int -> j:Int -> S.Set Int / [j - i] @-}
rng i j
  | i < j     = S.union (S.singleton i) (rng (i+1) j)
  | otherwise = S.empty
\end{code}

Equational Reasoning
--------------------

To build up a little intuition about the above
definition and how LH reasons about Sets, lets
write some simple "unit proofs".

First, lets check that `2` is indeed in the
set `rng 1 3`, by writing a type signature

\begin{code}
{-@ test1 :: () -> { S.member 2 (rng 1 3) } @-}
\end{code}

Any _implementation_ of the above type is a _proof_
that `2` is indeed in `rng 1 3`. Notice that we can
_reuse_ the operators from `Data.Set` (here, `S.member`)
to talk about set operations in the refinement logic.

We can construct a _proof_ of the above in an
[equational style][bird-algebra]:

\begin{code}
test1 ()
  =   S.member 2 (rng 1 3)
      -- by unfolding `rng 1 3`
  === S.member 2 (S.union (S.singleton 1) (rng 2 3))
      -- by unfolding `rng 2 3`
  === S.member 2 (S.union (S.singleton 1) (S.union (S.singleton 2) (rng 3 3)))
      -- by set-theory
  === True
  *** QED
\end{code}

the "proof" uses two library operators:

* **Implicit Equality"** [`e1 === e2`][lh-eq]
  checks that `e1` is indeed `e2` after
  **unfolding functions at most once**, and returns a term
  that equals both `e1` and `e2`, and

* [`e *** QED`][lh-qed] allows us to convert any term `e`
  into a `()` to complete a proof.

Thus, the first two steps of the above proof, simply unfold `rng`
and the final step follows from the SMT solver's "native" decision
procedure for sets which can _automatically_ verify equalities over
set operations like `S.union`, `S.singleton` and `S.member`.

Reusing Proofs
--------------

As a second example, lets check that:

\begin{code}
{-@ test2 :: () -> { S.member 2 (rng 0 3) } @-}
test2 ()
  =   S.member 2 (rng 0 3)
      -- (1) by unfolding `rng 0 3`
  === S.member 2 (S.union (S.singleton 0) (rng 1 3))
      -- (2) by set-theory
  === (2 == 0 || S.member 2 (rng 1 3))
      -- (3) by using ex1
  ==? True ? test1 ()

  *** QED
\end{code}

The first two steps are as before and we _could_ complete
the proof by continuing to unfold in the equational style.
However, `test1` already establishes that `S.member 2 (rng 1 3)`
and we can _reuse_ this using:

* **Explicit Equality** [`e1 ==? e2 ? pf`][lh-exp-eq]
  which checks that `e1` is indeed `e2` _using_ any extra
  facts asserted by the term `pf` (in addition to unfolding
  functions at most once), and returns a term
  that equals both `e1` and `e2`.


Proof by Logical Evaluation
---------------------------

Equational proofs like `test1` and `test2` often
have long chains of calculations that can be
tedious to spell out. Fortunately, we taught LH a new
trick called **Proof by Logical Evaluation** (PLE) that
shifts the burden of performing those calculations
onto the machine (if thats what the user wants.)

For example, PLE completely automates the above proofs above proofs:

\begin{code}
{-@ test1_ple :: () -> { S.member 2 (rng 1 3) } @-}
test1_ple () = ()

{-@ test2_ple :: () -> { S.member 2 (rng 0 3) } @-}
test2_ple () = ()
\end{code}

While automation is cool, it can be *very* helpful to first
write out all the steps of an equational proof, at least
while building up intuition.


Membership
----------

At this point, we have enough tools to start proving some
interesting facts about _range-sets_. For example, if `x`
is _outside_ the range `i..j` then it does not belong in
`rng i j`:

\begin{code}
{-@ lem_mem :: i:_ -> j:_ -> x:{_| x < i || j <= x} ->
                  {not (S.member x (rng i j))} / [j - i]
  @-}
\end{code}

**Proof by Induction**

We will prove the above ["by induction"][tag-induction]

A confession: I always had trouble understanding what
exactly _by induction_ really meant. Why was it it ok
to "do" induction on one thing but not another?

With LH, _induction is just recursion_. That is,

1. We can *recursively* use the same theorem we
   are trying to prove, but

2. We must make sure that the recursive function/proof
   _terminates_.

The proof makes this clear:

\begin{code}
lem_mem i j x
                -- BASE CASE
  | i >= j  =   not (S.member x (rng i j))
                -- by unfolding `rng i j`
            === not (S.member x S.empty)
                -- by set-theory
            === True

            *** QED

                -- INDUCTIVE CASE
  | i < j   =   not (S.member x (rng i j))
                -- by unfolding `rng i j`
            === not (S.member x (S.union (S.singleton i) (rng (i + 1) j)))
                -- by set-theory
            === (x /= i && not (S.member x (rng (i + 1) j)))
                -- (*) by "induction hypothesis"
            ==? True ? lem_mem (i + 1) j x

            *** QED
\end{code}

There are two cases.

- **Base Case** (`i >= j`) : Here `rng i j` is empty, so `x`
  cannot be in it.

- **Inductive Case** (`i < j`) : Here we unfold `rng i j` and
  then _recursively call_ `lem_mem (i+1) j` to obtain the fact
  that `x` cannot be in `i+1..j` to complete the proof.

LH automatically checks that the proof:

1. **Accounts for all cases**, as otherwise the
   function is _not total_ i.e. like the `head` function
   which is only defined on non-empty lists.
   (Try deleting a case at the [demo][demo] to see what happens.)

2. **Terminates**, as otherwise the induction is bogus (or in math-speak,
   not _well-founded_). For the latter, it uses the [termination metric][]


\begin{code}
{-@ lem_mem_ple :: i:_ -> j:_ -> x:{_| x < i || j <= x} ->
                     {not (S.member x (rng i j))} / [j - i]
  @-}
lem_mem_ple f t x
  | f < t     =  lem_mem_ple (f + 1) t x
  | otherwise =  ()
\end{code}

Disjointness
------------

- `lem_disj` -- EQ
- `lem_disj` -- PLE

\begin{code}
--------------------------------------------------------------------------------
-- | LEMMA: The range-sets of non-overlapping ranges is disjoint.
--------------------------------------------------------------------------------
{-@ lem_disj :: f1:_ -> t1:_ -> f2:{Int | t1 <= f2 } -> t2:Int  ->
                   { disjoint (rng f1 t1) (rng f2 t2) } / [t2 - f2] @-}
lem_disj :: Int -> Int -> Int -> Int -> ()
lem_disj f1 t1 f2 t2
  | f2 < t2   =   disjoint (rng f1 t1) (rng f2 t2)
              === disjoint (rng f1 t1) (S.union (S.singleton f2) (rng (f2 + 1) t2))
              === (disjoint (rng f1 t1) (rng (f2 + 1) t2) && not (S.member f2 (rng f1 t1)))
              ==? disjoint (rng f1 t1) (rng (f2 + 1) t2) ? lem_mem f1 t1 f2
              ==? True                                   ? lem_disj f1 t1 (f2 + 1) t2
              *** QED
  | otherwise =   disjoint (rng f1 t1) (rng f2 t2)
              === disjoint (rng f1 t1) S.empty
              === True
              *** QED

{-
{- lem_disj :: f1:_ -> t1:_ -> f2:{Int | t1 <= f2 } -> t2:Int  ->
                   { disjoint (rng f1 t1) (rng f2 t2) } / [t2 - f2] @-}
lem_disj :: Int -> Int -> Int -> Int -> ()
lem_disj f1 t1 f2 t2
  | f2 < t2   = lem_mem f1 t1 f2 &&& lem_disj f1 t1 (f2 + 1) t2
  | otherwise = ()
-}
\end{code}

Splitting
---------

- `lem_split_union` 	-- PLE
- `lem_split` 		    -- PLE

\begin{code}
{-@ inline disjointUnion @-}
disjointUnion :: S.Set Int -> S.Set Int -> S.Set Int -> Bool
disjointUnion s a b = s == S.union a b && disjoint a b

{-@ inline disjoint @-}
disjoint :: S.Set Int -> S.Set Int -> Bool
disjoint a b = (S.intersection a b) == S.empty
--------------------------------------------------------------------------------
-- | LEMMA: A range-set can be partitioned by any point within the range.
--------------------------------------------------------------------------------
{-@ lem_split :: f:_ -> x:{_ | f <= x} -> t:{_ | x <= t} ->
                   { disjointUnion (rng f t) (rng f x) (rng x t) } @-}
lem_split :: Int -> Int -> Int -> ()
lem_split f x t = lem_split_union f x t &&& lem_disj f x x t

{-@ lem_split_union :: f:_ -> x:{_ | f <= x} -> t:{_ | x <= t} ->
                        { rng f t = S.union (rng f x) (rng x t) } / [x - f]  @-}
lem_split_union :: Int -> Int -> Int -> ()
lem_split_union f x t
  | f == x    =   rng f t
              === S.union S.empty   (rng f t)
              === S.union (rng f f) (rng f t)
              *** QED

  | otherwise =   rng f t
              === S.union (S.singleton f) (rng (f+1) t)
              ==? S.union (S.singleton f) (S.union (rng (f+1) x) (rng x t))
                  ? lem_split_union (f + 1) x t
              === S.union (S.union (S.singleton f) (rng (f+1) x)) (rng x t)
              === S.union (rng f x) (rng x t)
              *** QED

{-
{- lem_split :: f:_ -> x:{_ | f <= x} -> t:{_ | x <= t} ->
                   { disjointUnion (rng f t) (rng f x) (rng x t) } / [x - f] @-}
lem_split :: Int -> Int -> Int -> ()
lem_split f x t
  | f == x    =  ()
  | otherwise =  lem_split (f + 1) x t &&& lem_mem x t f
-}
\end{code}

Set Operations
--------------

**Subset**

- `lem_sub`		      -- PLE

\begin{code}
--------------------------------------------------------------------------------
-- | LEMMA: The range-set of an interval is contained inside that of a larger.
--------------------------------------------------------------------------------
{-@ lem_sub :: f1:_ -> t1:{_ | f1 < t1} -> f2:_ -> t2:{_ | f2 < t2 && f2 <= f1 && t1 <= t2 } ->
                { S.isSubsetOf (rng f1 t1) (rng f2 t2) } @-}
lem_sub :: Int -> Int -> Int -> Int -> ()
lem_sub f1 t1 f2 t2 = lem_split f2 f1 t2
                  &&& lem_split f1 t1 t2
\end{code}

**Union**

- `lem_union`		    -- PLE

\begin{code}
--------------------------------------------------------------------------------
-- | LEMMA: The endpoints define the union of overlapping range-sets.
--------------------------------------------------------------------------------
{-@ lem_union :: f1:_ -> t1:{_ | f1 < t1} -> f2:_ -> t2:{_ | f2 < t2 && f1 <= t2 && t2 <= t1 } ->
                { rng (min f1 f2) t1 = S.union (rng f1 t1) (rng f2 t2) }   @-}
lem_union :: Int -> Int -> Int -> Int -> ()
lem_union f1 t1 f2 t2
  | f1 < f2   =    rng (min f1 f2) t1
              ===  rng f1 t1
              ==?  S.union (rng f1 t1) (rng f2 t2) ? lem_sub f2 t2 f1 t1
              *** QED

  | otherwise =   S.union (rng f1 t1) (rng f2 t2)
              ==? S.union (S.union (rng f1 t2) (rng t2 t1)) (S.union (rng f2 f1) (rng f1 t2))
                  ? (lem_split f1 t2 t1 &&& lem_split f2 f1 t2)
              === S.union (rng f2 f1) (S.union (rng f1 t2) (rng t2 t1))
              === S.union (rng f2 f1) (rng f1 t1)
              ==? rng f2 t1 ? lem_split f2 f1 t1
              === rng (min f1 f2) t1
              *** QED
{-
{- lem_union :: f1:_ -> t1:{_ | f1 < t1} -> f2:_ -> t2:{_ | f2 < t2 && f1 <= t2 && t2 <= t1 } ->
                { rng (min f1 f2) t1 = S.union (rng f1 t1) (rng f2 t2) }   @-}
lem_union :: Int -> Int -> Int -> Int -> ()
lem_union f1 t1 f2 t2
  | f1 < f2   = lem_sub f2 t2 f1 t1
  | otherwise = lem_split f2 f1 t1
            &&& lem_split f1 t2 t1
            &&& lem_split f2 f1 t2
-}
\end{code}

**Intersection**

- `lem_intersect` 	-- PLE

\begin{code}
--------------------------------------------------------------------------------
-- | LEMMA: The inner-points define the intersection of overlapping range-sets.
--------------------------------------------------------------------------------
{-@ lem_intersect :: f1:_ -> t1:{_ | f1 < t1} -> f2:_ -> t2:{_ | f2 < t2 && f1 <= t2 && t2 <= t1 } ->
                      { rng (max f1 f2) t2 = S.intersection (rng f1 t1) (rng f2 t2) }  @-}
lem_intersect :: Int -> Int -> Int -> Int -> ()
lem_intersect f1 t1 f2 t2
  | f1 < f2   =    rng (max f1 f2) t2
              ===  rng f2 t2
              ==?  S.intersection (rng f1 t1) (rng f2 t2)
                        ? lem_sub f2 t2 f1 t1
              *** QED

  | otherwise =    S.intersection (rng f1 t1) (rng f2 t2)
              ==?  (S.intersection (S.union (rng f1 t2) (rng t2 t1)) (S.union (rng f2 f1) (rng f1 t2)))
                        ? (lem_split f1 t2 t1 &&& lem_split f2 f1 t2)
              ==?  rng f1 t2
                        ? (lem_disj  f2 f1 f1 t1 &&& lem_disj  f2 t2 t2 t1)
              ===  rng (max f1 f2) t2
              ***  QED

{-
{- lem_intersect :: f1:_ -> t1:{_ | f1 < t1} -> f2:_ -> t2:{_ | f2 < t2 && f1 <= t2 && t2 <= t1 } ->
                      { rng (max f1 f2) t2 = S.intersection (rng f1 t1) (rng f2 t2) }  @-}
lem_intersect :: Int -> Int -> Int -> Int -> ()
lem_intersect f1 t1 f2 t2
  | f1 < f2   = lem_sub f2 t2 f1 t1
  | otherwise = lem_split f1 t2 t1
            &&& lem_split f2 f1 t2
            &&& lem_disj  f2 f1 f1 t1
            &&& lem_disj  f2 t2 t2 t1

-}
\end{code}

<div class="hidden">
\begin{code}
--------------------------------------------------------------------------------
-- | Some helper definitions
--------------------------------------------------------------------------------
{-@ reflect min @-}
min :: (Ord a) => a -> a -> a
min x y = if x < y then x else y

{-@ reflect max @-}
max :: (Ord a) => a -> a -> a
max x y = if x < y then y else x

rng         :: Int -> Int -> S.Set Int
test1       :: () -> ()
test2       :: () -> ()
test1_ple   :: () -> ()
test2_ple   :: () -> ()
lem_mem     :: Int -> Int -> Int -> ()
lem_mem_ple :: Int -> Int -> Int -> ()

-- https://ucsd-progsys.github.io/liquidhaskell-blog/tags/induction.html
\end{code}
</div>

[lh-qed]:            https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/NewProofCombinators.hs#L65-L69
[lh-imp-eq]:         https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/NewProofCombinators.hs#L87-L96
[lh-exp-eq]:         https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/NewProofCombinators.hs#L98-L116
[bird-algebra]:      http://themattchan.com/docs/algprog.pdf
[demo]:              http://goto.ucsd.edu:8090/index.html#?demo=RangeSet.hs
[intersect-good]:    https://github.com/antalsz/hs-to-coq/blob/8f84d61093b7be36190142c795d6cd4496ef5aed/examples/intervals/Proofs.v#L370-L439
[union-good]:        https://github.com/antalsz/hs-to-coq/blob/b7efc7a8dbacca384596fc0caf65e62e87ef2768/examples/intervals/Proofs_Function.v#L319-L382
[subtract-good]:     https://github.com/antalsz/hs-to-coq/blob/8f84d61093b7be36190142c795d6cd4496ef5aed/examples/intervals/Proofs.v#L565-L648
[tag-abs-ref]:      /tags/abstract-refinements.html
[tag-induction]:    /tags/induction.html
[hs-to-coq]:         https://github.com/antalsz/hs-to-coq
[nomeata-intervals]: https://www.joachim-breitner.de/blog/734-Finding_bugs_in_Haskell_code_by_proving_it
