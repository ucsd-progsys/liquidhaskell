---
layout: post
title: "Talking About Sets"
date: 2013-03-26 16:12
comments: true
external-url:
categories: basic measures sets
author: Ranjit Jhala
published: true 
demo: TalkingAboutSets.hs
---

In the posts so far, we've seen how LiquidHaskell allows you to use SMT 
solvers to specify and verify *numeric* invariants -- denominators 
that are non-zero, integer indices that are within the range of an 
array, vectors that have the right number of dimensions and so on.

However, SMT solvers are not limited to numbers, and in fact, support
rather expressive logics. In the next couple of posts, let's see how
LiquidHaskell uses SMT to talk about **sets of values**, for example, 
the contents of a list, and to specify and verify properties about 
those sets.

<!-- more -->

\begin{code}
module TalkingAboutSets where

import Data.Set hiding (filter, split)
import Prelude  hiding (reverse, filter)

\end{code}

Talking about Sets (In Logic)
=============================

First, we need a way to talk about sets in the refinement logic. We could
roll our own special Haskell type, but why not just use the `Set a` type
from `Data.Set`.

The `import Data.Set` , also instructs LiquidHaskell to import in the various 
specifications defined for the `Data.Set` module that we have *predefined* 
in [Data/Set.spec][setspec] 

\begin{code} Let's look at the specifications.
module spec Data.Set where

embed Set as Set_Set
\end{code}

The `embed` directive tells LiquidHaskell to model the **Haskell** 
type constructor `Set` with the **SMT** type constructor `Set_Set`.

\begin{code} First, we define the logical operators (i.e. `measure`s) 
measure Set_sng  :: a -> (Set a)                    -- ^ singleton
measure Set_cup  :: (Set a) -> (Set a) -> (Set a)   -- ^ union
measure Set_cap  :: (Set a) -> (Set a) -> (Set a)   -- ^ intersection
measure Set_dif  :: (Set a) -> (Set a) -> (Set a)   -- ^ difference 
\end{code}

\begin{code} Next, we define predicates on `Set`s 
measure Set_emp  :: (Set a) -> Prop                 -- ^ emptiness
measure Set_mem  :: a -> (Set a) -> Prop            -- ^ membership
measure Set_sub  :: (Set a) -> (Set a) -> Prop      -- ^ inclusion 
\end{code}


Interpreted Operations
----------------------

The above operators are *interpreted* by the SMT solver. 

\begin{code} That is, just like the SMT solver "knows that"
2 + 2 == 4
\end{code}

\begin{code} the SMT solver also "knows that"
(Set_sng 1) == (Set_cap (Set_sng 1) (Set_cup (Set_sng 2) (Set_sng 1)))
\end{code}

This is because, the above formulas belong to a decidable Theory of Sets
which can be reduced to McCarthy's more general [Theory of Arrays][mccarthy]. 
See [this recent paper][z3cal] if you want to learn more about how modern SMT 
solvers "know" the above equality holds...

Talking about Sets (In Code)
============================

Of course, the above operators exist purely in the realm of the 
refinement logic, beyond the grasp of the programmer.

To bring them down (or up, or left or right) within reach of Haskell code, 
we can simply *assume* that the various public functions in `Data.Set` do 
the *Right Thing* i.e. produce values that reflect the logical set operations:

\begin{code} First, the functions that create `Set` values
empty     :: {v:(Set a) | (Set_emp v)}
singleton :: x:a -> {v:(Set a) | v = (Set_sng x)}
\end{code}

\begin{code} Next, the functions that operate on elements and `Set` values
insert :: Ord a => x:a 
                -> xs:(Set a) 
                -> {v:(Set a) | v = (Set_cup xs (Set_sng x))}

delete :: Ord a => x:a 
                -> xs:(Set a) 
                -> {v:(Set a) | v = (Set_dif xs (Set_sng x))}
\end{code}

\begin{code} Then, the binary `Set` operators
union        :: Ord a => xs:(Set a) 
                      -> ys:(Set a) 
                      -> {v:(Set a) | v = (Set_cup xs ys)}

intersection :: Ord a => xs:(Set a) 
                      -> ys:(Set a) 
                      -> {v:(Set a) | v = (Set_cap xs ys)}

difference   :: Ord a => xs:(Set a) 
                      -> ys:(Set a) 
                      -> {v:(Set a) | v = (Set_dif xs ys)}
\end{code}

\begin{code} And finally, the predicates on `Set` values:
isSubsetOf :: Ord a => xs:(Set a) 
                    -> ys:(Set a) 
                    -> {v:Bool | (Prop v) <=> (Set_sub xs ys)}

member     :: Ord a => x:a 
                    -> xs:(Set a) 
                    -> {v:Bool | (Prop v) <=> (Set_mem x xs)}
\end{code}

**Note:** Of course we shouldn't and needn't really *assume*, but should and
will *guarantee* that the functions from `Data.Set` implement the above types. 
But thats a story for another day...

Proving Theorems With LiquidHaskell
===================================

OK, let's take our refined operators from `Data.Set` out for a spin!
One pleasant consequence of being able to precisely type the operators 
from `Data.Set` is that we have a pleasant interface for using the SMT
solver to *prove theorems* about sets, while remaining firmly rooted in
Haskell. 

First, let's write a simple function that asserts that its input is `True`

\begin{code}
{-@ boolAssert :: {v: Bool | (Prop v)} -> {v:Bool | (Prop v)} @-}
boolAssert True   = True
boolAssert False  = error "boolAssert: False? Never!"
\end{code}

Now, we can use `boolAssert` to write some simple properties. (Yes, these do
indeed look like QuickCheck properties -- but here, instead of generating
tests and executing the code, the type system is proving to us that the
properties will *always* evaluate to `True`) 

Let's check that `intersection` is commutative ...

\begin{code}
prop_cap_comm x y 
  = boolAssert 
  $ (x `intersection` y) == (y `intersection` x)
\end{code}

that `union` is associative ...

\begin{code}
prop_cup_assoc x y z 
  = boolAssert 
  $ (x `union` (y `union` z)) == (x `union` y) `union` z
\end{code}

and that `union` distributes over `intersection`.

\begin{code}
prop_cap_dist x y z 
  = boolAssert 
  $  (x `intersection` (y `union` z)) 
  == (x `intersection` y) `union` (x `intersection` z) 
\end{code}
  
Of course, while we're at it, let's make sure LiquidHaskell
doesn't prove anything that *isn't* true ...

\begin{code}
prop_cup_dif_bad x y
   = boolAssert 
   $ x == (x `union` y) `difference` y
\end{code}

Hmm. You do know why the above doesn't hold, right? It would be nice to
get a *counterexample* wouldn't it? Well, for the moment, there is
QuickCheck!

Thus, the refined types offer a nice interface for interacting with the SMT
solver in order to prove theorems in LiquidHaskell. (BTW, The [SBV project][sbv]
describes another approach for using SMT solvers from Haskell, without the 
indirection of refinement types.)

While the above is a nice warm up exercise to understanding how
LiquidHaskell reasons about sets, our overall goal is not to prove 
theorems about set operators, but instead to specify and verify 
properties of programs. 



The Set of Values in a List
===========================

Let's see how we might reason about sets of values in regular Haskell programs.

We'll begin with Lists, the jack-of-all-data-types. Now, instead of just
talking about the **number of** elements in a list, we can write a measure
that describes the **set of** elements in a list:

\begin{code} A measure for the elements of a list, from [Data/Set.spec][setspec]

measure listElts :: [a] -> (Set a) 
listElts ([])    = {v | (? Set_emp(v))}
listElts (x:xs)  = {v | v = (Set_cup (Set_sng x) (listElts xs)) }
\end{code}

That is, `(listElts xs)` describes the set of elements contained in a list `xs`.

Next, to make the specifications concise, let's define a few predicate aliases:

\begin{code}
{-@ predicate EqElts  X Y = 
      ((listElts X) = (listElts Y))                        @-}

{-@ predicate SubElts   X Y = 
      (Set_sub (listElts X) (listElts Y))                  @-}

{-@ predicate UnionElts X Y Z = 
      ((listElts X) = (Set_cup (listElts Y) (listElts Z))) @-}
\end{code}

A Trivial Identity
------------------

OK, now let's write some code to check that the `listElts` measure is sensible!

\begin{code}
{-@ listId    :: xs:[a] -> {v:[a] | (EqElts v xs)} @-}
listId []     = []
listId (x:xs) = x : listId xs
\end{code}

That is, LiquidHaskell checks that the set of elements of the output list
is the same as those in the input.

A Less Trivial Identity
-----------------------

Next, let's write a function to `reverse` a list. Of course, we'd like to
verify that `reverse` doesn't leave any elements behind; that is that the 
output has the same set of values as the input list. This is somewhat more 
interesting because of the *tail recursive* helper `go`. Do you understand 
the type that is inferred for it? (Put your mouse over `go` to see the 
inferred type.)

\begin{code}
{-@ reverse       :: xs:[a] -> {v:[a] | (EqElts v xs)} @-}
reverse           = go [] 
  where 
    go acc []     = acc
    go acc (y:ys) = go (y:acc) ys
\end{code}

Appending Lists
---------------

Next, here's good old `append`, but now with a specification that states
that the output indeed includes the elements from both the input lists.

\begin{code}
{-@ append       :: xs:[a] -> ys:[a] -> {v:[a]| (UnionElts v xs ys)} @-}
append []     ys = ys
append (x:xs) ys = x : append xs ys
\end{code}

Filtering Lists
---------------

Let's round off the list trilogy, with `filter`. Here, we can verify
that it returns a **subset of** the values of the input list.

\begin{code}
{-@ filter      :: (a -> Bool) -> xs:[a] -> {v:[a]| (SubElts v xs)} @-}

filter f []     = []
filter f (x:xs) 
  | f x         = x : filter f xs 
  | otherwise   = filter f xs
\end{code}

Merge Sort
==========

Let's conclude this entry with one larger example: `mergeSort`.
We'd like to verify that, well, the list that is returned 
contains the same set of elements as the input list. 

And so we will!

But first, let's remind ourselves of how `mergeSort` works:

1. `split` the input list into two halves, 
2. `sort`  each half, recursively, 
3. `merge` the sorted halves to obtain the sorted list.


Split
-----

We can `split` a list into two, roughly equal parts like so:

\begin{code}
split []     = ([], [])
split (x:xs) = (x:zs, ys)
  where 
    (ys, zs) = split xs
\end{code}

LiquidHaskell verifies that the relevant property of split is

\begin{code} 
{-@ split :: xs:[a] -> ([a], [a])<{\ys zs -> (UnionElts xs ys zs)}> @-}
\end{code}

The funny syntax with angle brackets simply says that the output of `split` 
is a *pair* `(ys, zs)` whose union is the list of elements of the input `xs`.
(Yes, this is indeed a dependent pair; we will revisit these later to
understand whats going on with the odd syntax.)

Merge
-----

Next, we can `merge` two (sorted) lists like so:

\begin{code}
merge xs []         = xs
merge [] ys         = ys
merge (x:xs) (y:ys) 
  | x <= y          = x : merge xs (y : ys)
  | otherwise       = y : merge (x : xs) ys
\end{code}

As you might expect, the elements of the returned list are the union of the
elements of the input, or as LiquidHaskell might say,

\begin{code}
{-@ merge :: (Ord a) => x:[a] -> y:[a] -> {v:[a]| (UnionElts v x y)} @-}
\end{code}

Sort
----

Finally, we put all the pieces together by

\begin{code}
{-@ mergeSort :: (Ord a) => xs:[a] -> {v:[a] | (EqElts v xs)} @-}
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort ys) (mergeSort zs) 
  where 
    (ys, zs)  = split xs
\end{code}

The type given to `mergeSort`guarantees that the set of elements in the 
output list is indeed the same as in the input list. Of course, it says 
nothing about whether the list is *actually sorted*. 

Well, Rome wasn't built in a day...

[sbv]:      https://github.com/LeventErkok/sbv
[setspec]:  https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/Set.spec
[mccarthy]: http://www-formal.stanford.edu/jmc/towards.ps
[z3cal]:    http://research.microsoft.com/en-us/um/people/leonardo/fmcad09.pdf
