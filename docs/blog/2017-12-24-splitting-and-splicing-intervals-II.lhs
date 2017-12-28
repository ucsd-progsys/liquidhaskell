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

However, [Hs-to-coq][hs-to-coq] let Breitner
specify and verify that his code properly
implemented a _set_ library. Today, lets
see how LH's new _"type-level computation"_
abilities let us reason about the sets
of values corresponding to intervals,
while using the SMT solver to greatly
simplify the overhead of proof.

(Click here to [demo][demo])

<!-- more -->

<div class="row">
<div class="col-lg-2"></div>
<div class="col-lg-8">
<img src="https://ucsd-progsys.github.io/liquidhaskell-blog/static/img/ribbon.png" alt="Ribbons">
</div>
<div class="col-lg-2"></div>
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
to (i.e. "the semantics of") an interval `i, j`
by importing the `Data.Set` library

\begin{code}
import qualified Data.Set as S
\end{code}

to write a function `rng i j` that defines the **range-set** `i..j`

\begin{code}
{-@ reflect rng @-}
{-@ rng :: i:Int -> j:Int -> S.Set Int / [j - i] @-}
rng i j
  | i < j     = S.union (S.singleton i) (rng (i+1) j)
  | otherwise = S.empty
\end{code}

The `reflect rng` [tells LH][tag-reflection] that
we are going to want to work with the Haskell
function `rng` at the refinement-type level.


Equational Reasoning
--------------------

To build up a little intuition about the above
definition and how LH reasons about Sets, lets
write some simple _unit proofs_. For example,
lets check that `2` is indeed in the range-set
`rng 1 3`, by writing a type signature

\begin{code}
{-@ test1 :: () -> { S.member 2 (rng 1 3) } @-}
\end{code}

Any _implementation_ of the above type is a _proof_
that `2` is indeed in `rng 1 3`. Notice that we can
reuse the operators from `Data.Set` (here, `S.member`)
to talk about set operations in the refinement logic.
Lets write this proof in an [equational style][bird-algebra]:

\begin{code}
test1 ()
  =   S.member 2 (rng 1 3)
      -- by unfolding `rng 1 3`
  === S.member 2 (S.union (S.singleton 1) (rng 2 3))
      -- by unfolding `rng 2 3`
  === S.member 2 (S.union (S.singleton 1)
                          (S.union (S.singleton 2) (rng 3 3)))
      -- by set-theory
  === True
  *** QED
\end{code}

the "proof" uses two library operators:

- `e1 === e2` is an [implicit equality][lh-imp-eq]
  that checks `e1` is indeed equal to `e2` after
  **unfolding functions at most once**, and returns
  a term that equals `e1` and `e2`, and

- `e *** QED` [converts any term][lh-qed] `e`
  into a proof.

The first two steps of `test1`, simply unfold `rng`
and the final step uses the SMT solver's
decision procedure for sets to check equalities
over set operations like `S.union`, `S.singleton`
and `S.member`.

Reusing Proofs
--------------

Next, lets check that:

\begin{code}
{-@ test2 :: () -> { S.member 2 (rng 0 3) } @-}
test2 ()
  =   S.member 2 (rng 0 3)
      -- by unfolding and set-theory
  === (2 == 0 || S.member 2 (rng 1 3))
      -- by re-using test1 as a lemma
  ==? True ? test1 ()
  *** QED
\end{code}

We could do the proof by unfolding in
the equational style. However, `test1`
already establishes that `S.member 2 (rng 1 3)`
and we can reuse this fact using:

- `e1 ==? e2 ? pf` which is an [explicit equality][lh-exp-eq]
  which checks that `e1` equals `e2` _because of_ the
  extra facts asserted by the `Proof` named `pf`
  (in addition to unfolding functions at most once)
  and returns a term that equals both `e1` and `e2`.

Proof by Logical Evaluation
---------------------------

Equational proofs like `test1` and `test2`
often have long chains of calculations that
can be tedious to spell out. Fortunately, we
taught LH a new trick called
**Proof by Logical Evaluation** (PLE) that
optionally shifts the burden of performing
those calculations onto the machine. For example,
PLE completely automates the above proofs:

\begin{code}
{-@ test1_ple :: () -> { S.member 2 (rng 1 3) } @-}
test1_ple () = ()

{-@ test2_ple :: () -> { S.member 2 (rng 0 3) } @-}
test2_ple () = ()
\end{code}

**Be Warned!** While automation is cool,
it can be *very* helpful to first write
out all the steps of an equational proof,
at least while building up intuition.


Proof by Induction
------------------

At this point, we have enough tools to start proving some
interesting facts about range-sets. For example, if `x`
is _outside_ the range `i..j` then it does not belong in
`rng i j`:

\begin{code}
{-@ lem_mem :: i:_ -> j:_ -> x:{x < i || j <= x} ->
                 { not (S.member x (rng i j)) } / [j - i]
  @-}
\end{code}

We will prove the above ["by induction"][tag-induction].
A confession: I always had trouble understanding what
exactly _proof by induction_ really meant. Why was it
it ok to "do" induction on one thing but not another?

**Induction is Recursion**

Fortunately, with LH, induction is just recursion. That is,

1. We can **recursively** use the same theorem we
   are trying to prove, but

2. We must make sure that the recursive function/proof
   **terminates**.

The proof makes this clear:

\begin{code}
lem_mem i j x
  | i >= j
      -- BASE CASE
  =   not (S.member x (rng i j))
      -- by unfolding
  === not (S.member x S.empty)
      -- by set-theory
  === True *** QED

  | i < j
      -- INDUCTIVE CASE
  =   not (S.member x (rng i j))
      -- by unfolding
  === not (S.member x (S.union (S.singleton i) (rng (i+1) j)))
      -- by set-theory
  === not (S.member x (rng (i+1) j))
      -- by "induction hypothesis"
  ==? True ? lem_mem (i + 1) j x *** QED
\end{code}

There are two cases.

- **Base Case:** As `i >= j`, we know `rng i j` is empty, so `x`
  cannot be in it.

- **Inductive Case** As `i < j` we can unfold `rng i j` and
  then _recursively call_ `lem_mem (i+1) j` to obtain the fact
  that `x` cannot be in `i+1..j` to complete the proof.

LH automatically checks that the proof:

1. **Accounts for all cases**, as otherwise the
   function is _not total_ i.e. like the `head` function
   which is only defined on non-empty lists.
   (Try deleting a case at the [demo][demo] to see what happens.)

2. **Terminates**, as otherwise the induction
   is bogus, or in math-speak, not _well-founded_.
   We use the [explicit termination metric][lh-termination]
   `/ [j-i]` as a hint to tell LH that in each recursive call,
   the size of the interval `j-i` shrinks and is
   always non-negative. LH checks that is indeed the case,
   ensuring that we have a legit proof by induction.

**Proof by Evaluation**

Once you get the hang of the above style, you get tired
of spelling out all the details. Logical evaluation lets
us eliminate all the boring calculational steps, leaving
the essential bits: the recursive (inductive) skeleton

\begin{code}
{-@ lem_mem_ple :: i:_ -> j:_ -> x:{x < i || j <= x} ->
                     {not (S.member x (rng i j))} / [j-i]
  @-}
lem_mem_ple i j x
  | i >= j =  ()
  | i < j  =  lem_mem_ple (i + 1) j x
\end{code}

The above is just `lem_mem` sans the
(PLE-synthesized) intermediate equalities.


Disjointness
------------

We say that two sets are _disjoint_ if their `intersection` is `empty`:

\begin{code}
{-@ inline disjoint @-}
disjoint :: S.Set Int -> S.Set Int -> Bool
disjoint a b = S.intersection a b == S.empty
\end{code}

Lets prove that two intervals are disjoint if
the first _ends_ before the second _begins_:

\begin{code}
{-@ lem_disj :: i1:_ -> j1:_ -> i2:{j1 <= i2} -> j2:_ ->
                  {disjoint (rng i1 j1) (rng i2 j2)} / [j2-i2]
  @-}
\end{code}

This proof goes "by induction" on the size of
the second interval, i.e. `j2-i2`:

\begin{code}
lem_disj i1 j1 i2 j2
  | i2 >= j2
      -- Base CASE
  =   disjoint (rng i1 j1) (rng i2 j2)
      -- by unfolding
  === disjoint (rng i1 j1) S.empty
      -- by set-theory
  === True
  *** QED

  | i2 < j2
      -- Inductive CASE
  =   disjoint (rng i1 j1) (rng i2 j2)
      -- by unfolding
  === disjoint (rng i1 j1) (S.union (S.singleton i2) (rng (i2+1) j2))
      -- by induction and lem_mem
  ==? True ? (lem_mem i1 j1 i2 &&& lem_disj i1 j1 (i2+1) j2)
  *** QED
\end{code}

Here, the operator `pf1 &&& pf2` conjoins the
two facts asserted by `pf1` and `pf2`.

Again, we can get PLE to do the boring calculations:

\begin{code}
{-@ lem_disj_ple :: i1:_ -> j1:_ -> i2:{j1 <= i2} -> j2:_ ->
                      {disjoint (rng i1 j1) (rng i2 j2)} / [j2-i2]
  @-}
lem_disj_ple i1 j1 i2 j2
  | i2 >= j2 = ()
  | i2 <  j2 = lem_mem i1 j1 i2 &&& lem_disj_ple i1 j1 (i2+1) j2
\end{code}


Splitting Intervals
-------------------

Finally, we can establish the **splitting property**
of an interval `i..j`, that is, given some `x` that lies
between `i` and `j` we can **split** `i..j` into `i..x`
and `x..j`. We define a predicate that a set `s` can
be split into `a` and `b` as:

\begin{code}
{-@ inline split @-}
split :: S.Set Int -> S.Set Int -> S.Set Int -> Bool
split s a b = s == S.union a b && disjoint a b
\end{code}

We can now state and prove the **splitting property** as:

\begin{code}
{-@ lem_split :: i:_ -> x:{i <= x} -> j:{x <= j} ->
                   {split (rng i j) (rng i x) (rng x j)} / [x-i]
  @-}
lem_split i x t
  | i == x = ()
  | i <  x = lem_split (i + 1) x t &&& lem_mem x t i
\end{code}

(We're using PLE here quite aggressively, can _you_ work out the equational proof?)


Set Operations
--------------

The splitting abstraction is a wonderful hammer that lets us
break higher-level proofs into the bite sized pieces suitable
for the SMT solver's decision procedures.

**Subset**

An interval `i1..j1` is _enclosed by_ `i2..j2`
if `i2 <= i1 < j1 <= j2`. Lets verify that the
range-set of an interval is **contained** in
that of an enclosing one.

\begin{code}
{-@ lem_sub :: i1:_ -> j1:{i1 < j1} ->
               i2:_ -> j2:{i2 < j2 && i2 <= i1 && j1 <= j2 } ->
                 { S.isSubsetOf (rng i1 j1) (rng i2 j2) }
  @-}
\end{code}

Here's a "proof-by-picture". We can split the
larger interval `i2..j2` into smaller pieces,
`i2..i1`, `i1..j1` and `j1..j2` one of which
is the `i1..j1`, thereby completing the proof:

<br>
<div class="row">
  <div class="col-lg-2"></div>
  <div class="col-lg-8">
  ![`lem_sub` a proof by picture](/static/img/lem_sub.png "lem_sub proof by picture")
  </div>
  <div class="col-lg-2"></div>
</div>
<br>

The intuition represented by the picture can distilled
into the following proof, that invokes `lem_split` to
carve `i2..j2` into the relevant sub-intervals:

\begin{code}
lem_sub i1 j1 i2 j2 = lem_split i2 i1 j2 &&& lem_split i1 j1 j2
\end{code}

**Union**

An interval `i1..j1` _overlaps_ `i2..j2`
if `i1 <= j2 <= i2`, that is, if the latter
ends somewhere inside the former.
The same splitting hammer lets us compute
the union of two overlapping intervals
simply by picking the interval defined
by the _endpoints_.

\begin{code}
{-@ lem_union ::
      i1:_ -> j1:{i1 < j1} ->
      i2:_ -> j2:{i2 < j2 && i1 <= j2 && j2 <= j1 } ->
        { rng (min i1 i2) j1 = S.union (rng i1 j1) (rng i2 j2) }
  @-}
\end{code}

<br>
<div class="row">
  <div class="col-lg-2"></div>
  <div class="col-lg-8">
  ![`lem_union` a proof by picture](/static/img/lem_union.png "lem_union proof by picture")
  </div>
  <div class="col-lg-2"></div>
</div>
<br>

The pictorial proof illustrates the two cases:

1. `i1..j1` encloses `i2..j2`; here the union is just `i1..j1`,

2. `i1..j1` only overlaps `i1..j1`; here the union is `i2..j1` which
   can be split into `i2..i1`, `i1..j2` and `j2..j1` which are exactly
   the union of the intervals `i1..j1` and `i2..j2`.

Again, we render the picture into a formal proof as:

\begin{code}
lem_union i1 j1 i2 j2
  -- i1..j1 encloses i2..j2
  | i1 < i2   = lem_sub i2 j2 i1 j1
  -- i1..j1 overlaps i2..j2
  | otherwise = lem_split i2 i1 j1
            &&& lem_split i1 j2 j1
            &&& lem_split i2 i1 j2
\end{code}

**Intersection**

Finally, we check that the intersection of two overlapping intervals
is given by their _inner-points_.

\begin{code}
{-@ lem_intersect ::
      i1:_ -> j1:{i1 < j1} ->
      i2:_ -> j2:{i2 < j2 && i1 <= j2 && j2 <= j1 } ->
        {rng (max i1 i2) j2 = S.intersection (rng i1 j1) (rng i2 j2)}
  @-}
\end{code}

<br>
<div class="row">
  <div class="col-lg-2"></div>
  <div class="col-lg-8">
  ![`lem_intersect` a proof by picture](/static/img/lem_intersect.png "lem_intersect proof by picture")
  </div>
  <div class="col-lg-2"></div>
</div>
<br>

We have the same two cases as for `lem_union`

1. `i1..j1` encloses `i2..j2`; here the intersection is just `i2..j2`,

2. `i1..j1` only overlaps `i1..j1`; here the intersection is the
   _middle segment_ `i1..j2`, which we obtain by
   (a) _splitting_ `i1..j1` at `j2`,
   (b) _splitting_ `i2..j2` at `i1`,
   (c) _discarding_ the end segments which do not belong in the intersection.

\begin{code}
lem_intersect i1 j1 i2 j2
  -- i1..j1 encloses i2..j2
  | i1 < i2   = lem_sub i2 j2 i1 j1
  -- i1..j1 overlaps i2..j2
  | otherwise = lem_split i1 j2 j1
            &&& lem_split i2 i1 j2
            &&& lem_disj  i2 i1 i1 j1     -- discard i2..i1
            &&& lem_disj  i2 j2 j2 j1     -- discard j2..j1
\end{code}


Conclusions
-----------

Whew. That turned out a lot longer than I'd expected!

On the bright side, we saw how to:

1. _Specify_ the semantics of range-sets,
2. _Write_   equational proofs using plain Haskell code,
3. _Avoid_   boring proof steps using PLE,
4. _Verify_  key properties of operations on range-sets.

Next time we'll finish the series by showing how to use
the above lemmas to specify and verify the correctness
of [Breitner's implementation][nomeata-intervals].


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
lem_mem      :: Int -> Int -> Int -> ()
lem_mem_ple  :: Int -> Int -> Int -> ()
lem_sub      :: Int -> Int -> Int -> Int -> ()
lem_disj     :: Int -> Int -> Int -> Int -> ()
lem_disj_ple :: Int -> Int -> Int -> Int -> ()
lem_split :: Int -> Int -> Int -> ()

lem_intersect :: Int -> Int -> Int -> Int -> ()
lem_union :: Int -> Int -> Int -> Int -> ()
-- https://ucsd-progsys.github.io/liquidhaskell-blog/tags/induction.html

\end{code}
</div>

[splicing-1]:        https://ucsd-progsys.github.io/liquidhaskell-blog/2017/12/15/splitting-and-splicing-intervals-I.lhs/
[lh-termination]:    https://github.com/ucsd-progsys/liquidhaskell/blob/develop/README.md#explicit-termination-metrics
[lh-qed]:            https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/NewProofCombinators.hs#L65-L69
[lh-imp-eq]:         https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/NewProofCombinators.hs#L87-L96
[lh-exp-eq]:         https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/NewProofCombinators.hs#L98-L116
[bird-algebra]:      http://themattchan.com/docs/algprog.pdf
[demo]:              http://goto.ucsd.edu:8090/index.html#?demo=RangeSet.hs
[intersect-good]:    https://github.com/antalsz/hs-to-coq/blob/8f84d61093b7be36190142c795d6cd4496ef5aed/examples/intervals/Proofs.v#L370-L439
[union-good]:        https://github.com/antalsz/hs-to-coq/blob/b7efc7a8dbacca384596fc0caf65e62e87ei2768/examples/intervals/Proofs_Function.v#L319-L382
[subtract-good]:     https://github.com/antalsz/hs-to-coq/blob/8f84d61093b7be36190142c795d6cd4496ef5aed/examples/intervals/Proofs.v#L565-L648
[tag-abs-ref]:       /tags/abstract-refinements.html
[tag-induction]:     /tags/induction.html
[tag-reflection]:    /tags/reflection.html
[hs-to-coq]:         https://github.com/antalsz/hs-to-coq
[nomeata-intervals]: https://www.joachim-breitner.de/blog/734-Finding_bugs_in_Haskell_code_by_proving_it
