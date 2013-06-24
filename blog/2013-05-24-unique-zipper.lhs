---
layout: post
title: "Unique Zippers"
date: 2013-05-10 16:12
comments: true
external-url:
categories: basic measures sets zipper uniqueness
author: Niki Vazou
published: true
demo: UniqueZipper.hs
---

**The story so far:** [Previously][about-sets] we saw
how we can use LiquidHaskell to talk about set of values
and specifically the *set of values* in a list.

Often, we want to enforce the invariant that a particular data structure
contains *no duplicates*. For example, we may have a structure that holds
a collection of file handles, or other resources, where the presence of
duplicates could lead to unpleasant leaks.

In this post, we will see how to use LiquidHaskell to talk
about the set of duplicate values in data structures, and 
hence, let us specify and verify uniqueness, that is, the
absence of duplicates.

<!-- more -->

To begin, lets extend our vocabulary to talk about the *set of duplicate
values* in lists.  By constraining this set to be empty, we can specify a
list without duplicates, or an **unique list**.  Once we express uniqueness
on lists, it is straightforward to describe uniqueness on other data
structures that contain lists.  As an example, we will illustrate the
properties of a **unique zipper**.

\begin{code}
module UniqueZipper where

import Prelude  hiding (reverse, (++), filter)
import Data.Set hiding (filter)
\end{code}


A Quick Recap
=============

\begin{code} In the previous post we used a measure for the elements of a list, from [Data/Set.spec][setspec]
measure listElts :: [a] -> (Set a)
listElts ([])    = {v | (? (Set_emp v))}
listElts (x:xs)  = {v | v = (Set_cup (Set_sng x) (listElts xs)) }
\end{code}

With this measure we defined predicate aliases 
that describe relations between lists:

\begin{code}
{-@ predicate EqElts  X Y      = 
      ((listElts X) = (listElts Y))                        @-}

{-@ predicate DisjointElts X Y = 
      (Set_emp (Set_cap (listElts X) (listElts Y)))        @-}

{-@ predicate SubElts X Y      = 
      (Set_sub (listElts X) (listElts Y))                  @-}

{-@ predicate UnionElts X Y Z  = 
      ((listElts X) = (Set_cup (listElts Y) (listElts Z))) @-}

{-@ predicate ListElt N X      = 
      (Set_mem N (listElts X))                             @-}
\end{code}


These predicates were our vocabulary on specifying properties of list functions.
Remember, that `reverse` returns an output list that has the same elements, i.e., `EqElts`, with the input list.
We can extend these predicates and express list uniqueness.
So reversing a unique list should again return an output list that has the same
elements as the input list, and also it is unique.

Describing Unique Lists
======================

To describe unique lists, we follow two steps:

1. we describe the set of duplicate values of a list; and 
2. we demand this set to be empty.

Towards the first step, we define a measure `dups`
that returns the duplicate values of its input list.
This measure is recursively defined:
The duplicates of an empty list is the empty set.
We compute the duplicates of a non-empty list, 
namely `x:xs`, as follows:

- If `x` is an element of `xs`, then `x` is a duplicate.
  Hence, `dups` is `x` plus the (recursively computed) 
  duplicates in `xs`.

- Otherwise, we can ignore `x` and recursively compute 
  the duplicates of `xs`.

The above intuition can be formalized as a measure:

\begin{code}
{-@
  measure dups :: [a] -> (Set a)
  dups([])   = {v | (? (Set_emp v))}
  dups(x:xs) = {v | v = (if (Set_mem x (listElts xs))
                         then (Set_cup (Set_sng x) (dups xs))
                         else (dups xs)) }
  @-}
\end{code}

With `dups` in hand, it is direct to describe unique lists:

A list is unique, if the set of duplicates, as computed by `dups` is empty.

We create a type alias for unique lists and name it `UList`.

\begin{code}
{-@ predicate ListUnique X = (Set_emp (dups X)) @-}

{-@ type UList a = {v:[a] | (ListUnique v)}     @-}
\end{code}


Functions on Unique Lists
==========================

In the previous post, we proved interesting properties about 
the list trilogy, i.e., `append`, `reverse`, and `filter`.
Now, we will prove that apart from these properties,
all these functions preserve list uniqueness.

Append
------

To begin with, we proved that the output of append
indeed includes the elements from both the input lists.
Now, we can also prove that if both input lists are 
unique *and their elements are disjoint*, then the 
output list is also unique.

\begin{code}
infixr 5 ++
{-@ UniqueZipper.++ :: xs:(UList a)
                    -> ys:{v: UList a | (DisjointElts v xs)}
                    -> {v: UList a | (UnionElts v xs ys)}
  @-}
(++)         :: [a] -> [a] -> [a]
[] ++ ys     = ys
(x:xs) ++ ys = x:(xs ++ ys)
\end{code}

Reverse
-------

Next, we can prove that if a unique list is reversed, 
the output list has the same elements as the input,
and also it is unique.

\begin{code}
{-@ reverse :: xs:(UList a) -> {v: UList a | (EqElts v xs)} @-}
reverse :: [a] -> [a]
reverse = go []
  where
    go a []     = a
    go a (x:xs) = go (x:a) xs 
\end{code}

Filter
------

Finally, filtering a unique list returns a list with a subset of
values of the input list, that once again is unique! 

\begin{code}
{-@ filter :: (a -> Bool) 
           -> xs:(UList a) 
           -> {v:UList a | (SubElts v xs)} 
  @-}
filter p [] = []
filter p (x:xs) 
  | p x       = x : filter p xs
  | otherwise = filter p xs
\end{code}


Unique Zipper
=============

That was easy enough! Now, lets look at a slightly more interesting
structure fashioned from lists.  A [zipper][wiki-zipper] is an aggregate
data stucture that is used to arbitrary traverse the structure and update
its contents.

We define a zipper as a data type that contains an element (called `focus`)
that we are currently using, a list of elements (called `up`) before
the current one, and a list of elements (called `down`) after the current one.

\begin{code}
data Zipper a = Zipper { focus :: a       -- focused element in this set
                       , up    :: [a]     -- elements to the left
                       , down  :: [a] }   -- elements to the right
\end{code}


One well-known application of zippers is in the
[XMonad](http://xmonad.org/) tiling window manager. 
The set of windows being managed is stored in a zipper 
similar to the above. The `focus` happily coincides with 
the window currently in focus, and the `up` and `down` 
to the list of windows that come before and after it.

One crucial invariant maintained by XMonad is that the zipper structure is
unique -- i.e. each window appears at most once inside the zipper.

Lets see how we can state and check that all the values in a zipper are unique.

To start with, we would like to refine the `Zipper` data declaration
to express that both the lists in the structure are unique **and** 
do not include `focus` in their values.

LiquidHaskell allow us to refine data type declarations, using the liquid comments.
So, apart from above definition definition for the `Zipper`, we add a refined one,
stating that the data structure always enjoys the desired properties.

\begin{code}
{-@ data Zipper a = Zipper { focus :: a
                           , up    :: UListDif a focus
                           , down  :: UListDif a focus}
  @-}

{-@ type UListDif a N = {v:(UList a) | (not (ListElt N v))} @-}
\end{code}

It is worth noting that the above is kind of *dependent* record in that
the types of the `up` and `down` fields depend on the value of the `focus`
field.

With this annotation any time we use a `Zipper` in the code LiquidHaskell
knows that the `up` and `down` components are unique lists
that do not include `focus`. Moreover, when a new `Zipper` is constructed
LiquidHaskell proves that this property holds, otherwise a liquid type 
error is reported.


Hold on a minute!

The awake reader will have noticed that values inside the `Zipper` as 
specified so far, are *not unique*, as nothing prevents a value from 
appearing in both the `up` and the `down` components.

So, we have to specify that the contents of those two fields are *disjoint*.

One way to achieve this is by defining two measures `getUp` and `getDown`
that return the relevant parts of the `Zipper`

\begin{code}
{-@ measure getUp :: forall a. (Zipper a) -> [a] 
    getUp (Zipper focus up down) = up
  @-}

{-@ measure getDown :: forall a. (Zipper a) -> [a] 
    getDown (Zipper focus up down) = down
  @-}
\end{code}

With these definitions, we create a type alias `UZipper`
that states that the two list components are disjoint, and hence,
that we have a *unique zipper* with no duplicates.

\begin{code}
{-@ 
  type UZipper a = {v:Zipper a | (DisjointElts (getUp v) (getDown v))} 
  @-}
\end{code}


Functions on Unique Zippers
===========================

Now that we have defined a unique zipper, it is straightforward for
LiquidHaskell to prove that operations on zippers preserve uniqueness.

Differentiation
---------------

We can prove that a zipper that built from elements from a unique list is
indeed unique.

\begin{code}
{-@ differentiate :: UList a -> Maybe (UZipper a) @-}
differentiate []     = Nothing
differentiate (x:xs) = Just $ Zipper x [] xs
\end{code}

Integration
-----------

And vice versa, all elements of a unique zipper yield a unique list.

\begin{code}
{-@ integrate :: UZipper a -> UList a @-}
integrate (Zipper x l r) = reverse l ++ x : r
\end{code}

Recall the types for `++` and `reverse` that we proved earlier -- hover
your mouse over the identifiers to refresh your memory. Those types are
essential for establishing the type of `integrate`. 

- By the definition of `UZipper` we know that `l` is a unique list
  and that `x` is not an element of `l`.

- Thus via the type of `reverse` we know that  `reverse l` is also
  unique and disjoint from `x` and `r`.

- Finally, using the previously established type for `++` 
  LiquidHaskell can prove that since `x : r` is a unique 
  list with elements disjoint from `reverse l` the concatenation
  of the two lists is also a unique list.


With the exact same reasoning, we use the above list operations to create more zipper operations.

Reverse
-------

We can reverse a unique zipper

\begin{code}
{-@ reverseZipper :: UZipper a -> UZipper a @-}
reverseZipper :: Zipper a -> Zipper a
reverseZipper (Zipper t ls rs) = Zipper t rs ls
\end{code}

Shifting Focus
--------------

More the focus up or down

\begin{code}
{-@ focusUp   :: UZipper a -> UZipper a @-}
focusUp (Zipper t [] rs)     = Zipper x xs [] 
  where 
    (x:xs)                   = reverse (t:rs)

focusUp (Zipper t (l:ls) rs) = Zipper l ls (t:rs)

{-@ focusDown :: UZipper a -> UZipper a @-}
focusDown = reverseZipper . focusUp . reverseZipper
\end{code}

Filter
------

Finally, using the filter operation on lists allows LiquidHaskell to prove
that filtering a zipper also preserves uniqueness.

\begin{code}
{-@ filterZipper :: (a -> Bool) -> UZipper a -> Maybe (UZipper a) @-}
filterZipper p (Zipper f ls rs) 
  = case filter p (f:rs) of
      f':rs' -> Just $ Zipper f' (filter p ls) rs'
      []     -> case filter p ls of                  
                  f':ls' -> Just $ Zipper f' ls' []
                  []     -> Nothing
\end{code}

Conclusion
==========

That's all for now! This post illustrated

1. How we can use set theory to express properties the values of the list,
   such as list uniqueness.

2. How we can use LuquidHaskell to prove that these properties are
   preserved through list operations.

3. How we can embed this properties in complicated data structures that use
   lists, such as a zipper.


[wiki-zipper]: http://en.wikipedia.org/wiki/Zipper_(data_structure)
[about-sets]:  blog/2013/03/26/talking-about-sets.lhs/
[setspec]:     https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/Set.spec

\begin{code}
-- TODO: Dummy function to provide qualifier hint.
{-@ q :: x:a ->  {v:[a] |(not (Set_mem x (listElts v)))} @-}
q :: a -> [a]
q _ = []
\end{code}


