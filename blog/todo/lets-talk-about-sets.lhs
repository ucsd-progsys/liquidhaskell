
---
layout: post
title: "Lets Talk About Sets"
date: 2013-01-05 16:12
comments: true
external-url:
categories: basic, measures, sets
author: Ranjit Jhala
published: false 
---

In posts so far, we've seen how LiquidHaskell allows you to use SMT solvers
to specify and verify *numeric* invariants -- denominators that are
non-zero, integer indices that are within the range of an array, 
vectors that have the right number of dimensions and so on.

However, SMT solvers are not limited to numbers, and in fact, support rather 
expressive logics. In the next couple of posts, lets see how LiquidHaskell
uses SMT to talk about **sets of values**, for example, the contents of a 
list, and to specify and verify properties about those sets.

\begin{code}
module ListSets where
\end{code}

Talking about Sets (In Logic)
-----------------------------

First, we need a way to talk about sets in the refinement logic. We could
roll our own special Haskell type, but why not just use the `Set a` type
from `Data.Set`.

\begin{code}
import Data.Set 
\end{code}

The above, also instructs LiquidHaskell to import in the various 
specifications defined for the `Data.Set` module that we have *predefined* 
in [Data/Set.spec][setspec] 

Lets look at the specifications.

\begin{code} The `embed` directive tells LiquidHaskell to model the **Haskell** 
type constructor `Set` with the **SMT** type constructor `Set_Set`.

module spec Data.Set where

embed Set as Set_Set
\end{code}

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


**Interpreted Operations:**  The above operators are *interpreted* by 
the SMT solver. That is, just like the SMT solver *"knows that"* 

    2 + 2 == 4

the SMT solver *"knows that"* 

    (Set_sng 1) == (Set_cap (Set_sng 1) (Set_cup (Set_sng 2) (Set_sng 1)))

This is because, the above formulas belong to a decidable Theory of Sets
which can be reduced to McCarthy's more general [Theory of Arrays][mccarthy]. 
See [this recent paper][z3cal] if you want to learn more about how modern SMT 
solvers *"know"* the above equality holds...

Talking about Sets (In Code)
----------------------------

Of course, the above operators exist purely in the realm of the 
refinement logic, beyond the grasp of the programmer.

To bring them down (or up, or left or right) within reach of Haskell code, 
we can simply *assume* that the various public functions in `Data.Set` do 
the *Right Thing* i.e. produce values that reflect the logical set operations:

\begin{code} First, the functions that create `Set` values
empty         :: {v:(Set a) | (Set_emp v)}
singleton     :: x:a -> {v:(Set a) | v = (Set_sng x)}
\end{code}

\begin{code} Next, the functions that operate on elements and `Set` values
insert        :: Ord a => x:a -> xs:(Set a) -> {v:(Set a) | v = (Set_cup xs (Set_sng x))}
delete        :: Ord a => x:a -> xs:(Set a) -> {v:(Set a) | v = (Set_dif xs (Set_sng x))}
\end{code}

\begin{code} Then, the binary `Set` operators
union         :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = (Set_cup xs ys)}
intersection  :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = (Set_cap xs ys)}
difference    :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = (Set_dif xs ys)}
\end{code}

\begin{code} And finally, the predicates on `Set` values:
isSubsetOf    :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:Bool | (Prop v) <=> (Set_sub xs ys)}
member        :: Ord a => x:a -> xs:(Set a) -> {v:Bool | (Prop v) <=> (Set_mem x xs)}
\end{code}


**Note:** Ok fine, we shouldn't and needn't really *assume*, but should and
will *guarantee* that the functions from `Data.Set` implement the above types. 
But thats a story for another day...


Proving Theorems In Haskell
---------------------------

The Set of Values in a List
---------------------------

Merge Sort
----------






First, lets import the type `Set a` that represents sets


Next, lets write a measure for the set of elements in a list.
The measure is a simple recursive function that computes the set
by structural recursion on the list.

\begin{code} A measure for the elements of a list
{-@ measure elts :: [a] -> (Set a) 
    elts ([])   = {v | (? Set_emp(v))}
    elts (x:xs) = {v | v = (Set_cup (Set_sng x) (elts xs)) }
  @-}
\end{code}

\begin{code} we tell the solver to interpret `Set` *natively* in the refinement logic, via the solver's built in sort.
{-@ embed Set as Set_Set @-}
\end{code}

OK, now we can write some specifications!

A Trivial Identity
------------------

To start with, lets check that the `elts` measure is sensible.

\begin{code}
{-@ myid :: xs:[a] -> {v:[a]| (elts v) = (elts xs)} @-}
myid []     = []
myid (x:xs) = x : myid xs
\end{code}

A Less Trivial Identity
-----------------------

Next, lets write a function `myreverse` that reverses a list. 
Of course, it should also preserve the set of values thats in 
the list. This is somewhat more interesting because of the 
*tail recursive* helper `go`. Mouse over and see what type 
is inferred for it!

\begin{code}
{-@ myreverse :: xs:[a] -> {v:[a]| (elts v) = (elts xs)} @-}
myreverse = go [] 
  where 
    go acc []     = acc
    go acc (y:ys) = go (y:acc) ys
\end{code}

Appending Lists
---------------

Next, here's good old append, but now with a specification that states
that the output indeed includes the elements from both the input lists.

\begin{code}
{-@ myapp :: xs:[a] -> ys:[a] -> {v:[a] | (elts v) = (Set_cup (elts xs) (elts ys))} @-}
myapp []     ys = ys
myapp (x:xs) ys = x : myapp xs ys
\end{code}

Filtering Lists
---------------

Finally, to round off this little demo, here's `filter`. We can verify
that it returns a subset of the values of the input list.

\begin{code}
{-@ myfilter :: (a -> Bool) -> xs:[a] -> {v:[a]| (? (Set_sub (elts v) (elts xs)))} @-}
myfilter f []     = []
myfilter f (x:xs) 
  | f x           = x : myfilter f xs 
  | otherwise     = myfilter f xs
\end{code}



[setspec]:  https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/Set.spec
[mccarthy]: http://www-formal.stanford.edu/jmc/towards.ps
[z3cal]:    http://research.microsoft.com/en-us/um/people/leonardo/fmcad09.pdf


