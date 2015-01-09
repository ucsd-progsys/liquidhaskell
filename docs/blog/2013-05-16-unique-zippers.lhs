---
layout: post
title: "Unique Zippers"
date: 2013-05-10 16:12
comments: true
external-url:
categories: basic measures sets zipper uniqueness
author: Niki Vazou
published: false 
demo: TalkingAboutUniqueSets.hs
---

**The story so far:** [Previously][talking-about-sets] we saw
how we can use LiquidHaskell to talk about set of values and specifically
the set of values in a list.

In this post, we will extend this vocabulary to talk about the 
set of duplicate values in a list. 
If we constrain this set to be empty, 
we encode a list without duplicates, or an **unique list**. 
Once we express uniqueness on lists, it is straightforward to 
describe uniqueness on other data structures that contain lists.
As an example, we will illustrate the properties of a **unique zipper**.

\begin{code}
module UniqueZipper where

import Prelude  hiding (reverse, (++), filter)
import Data.Set hiding (filter)
\end{code}


A Quick Recap
=============

\begin{code} In the previous post we used a measure for the elements of a list, from [Data/Set.spec][setspec]
measure listElts :: [a] -> (Set a)
listElts ([])    = {v | (? Set_emp(v))}
listElts (x:xs)  = {v | v = (Set_cup (Set_sng x) (listElts xs)) }
\end{code}

With this measure we defined predicate aliases 
that describe relations between lists:

\begin{code}
{-@ predicate EqElts  X Y      = ((listElts X) = (listElts Y))                        @-}

{-@ predicate DisjointElts X Y = (Set_emp (Set_cap (listElts X) (listElts Y)))        @-}

{-@ predicate SubElts X Y      = (Set_sub (listElts X) (listElts Y))                  @-}

{-@ predicate UnionElts X Y Z  = ((listElts X) = (Set_cup (listElts Y) (listElts Z))) @-}

{-@ predicate ListElt N X      = (Set_mem N (listElts X))                             @-}
\end{code}


These predicates were our vocabulary on specifying properties of list functions.
Remember, that `reverse` returns an output list that has the same elements, i.e., `EqElts`, with the input list.
We can extend these predicates and express list uniqueness.
So reversing a unique list should again return an output list that has the same
elements as the input list, and also it is unique.

Describing Unique Lists
======================

To describe unique lists, we follow two steps:
first, we describe the set of duplicate values of
a list;
then, we demand this set to be empty.

Towards the first step, we define a measure `listDup`
that returns the duplicate values of its input list.
This measure is recursively defined:
The duplicates of an empty list is the empty set.
We compute the duplicates of a non-empty list, 
namely `x:xs`, as follows:

- If `x` is member of the list values of `xs`, then `x` is a duplicate
so `listDup` returns a set that contains `x` and the 
list duplicates of `xs`, as computed recursively.

- Otherwise, we can ignore `x` and recursively compute the duplicates of `xs`.

\begin{code}
{-@
  measure listDup :: [a] -> (Set a)
  listDup([])   = {v | (? (Set_emp v))}
  listDup(x:xs) = {v | v = ((Set_mem x (listElts xs))?(Set_cup (Set_sng x) (listDup xs)):(listDup xs)) }
  @-}
\end{code}

With `listDup` at hand, it is direct to describe unique lists.
A list is unique, if the set of duplicates, 
as computed by `listDup`
is the empty set.
We create a type alias for unique lists and name it `UList`.

\begin{code}
{-@ predicate ListUnique X = (Set_emp (listDup X)) @-}

{-@ type UList a = {v:[a] | (ListUnique v)}        @-}
\end{code}


Functions on Unique Lists
==========================

In the previous post, we proved interesting properties about 
the list trilogy, i.e., `append`, `reverse`, and `filter`.
Now, we will prove that apart from these properties,
all these function preserve list uniqueness.

To begin with, 
we proved that the output of append
indeed includes the elements from both the input lists.
Now, we can also prove that if both input lists are unique and 
their values form disjoint sets, then the output list is also unique.

\begin{code}
infixr 5 ++
{-@ UniqueZipper.++ :: xs:(UList a)
                    -> ys:{v: UList a | (DisjointElts v xs)}
                    -> {v: UList a | (UnionElts v xs ys)}
  @-}
(++)         :: [a] -> [a] -> [a]
[] ++ ys     = ys
(x:xs) ++ ys = x: (xs ++ ys)
\end{code}

Next, we can prove that if a unique list is reversed, 
the output list has the same elements as the input,
and also it is unique.
\begin{code}
{-@ reverse :: xs:(UList a)
            -> {v: UList a | (EqElts v xs)} 
  @-}
reverse :: [a] -> [a]
reverse = go []
  where
    go a []     = a
    go a (x:xs) = go (x:a) xs 
\end{code}

Finally, filtering a unique list returns a list
with a subset of values of the input list, that once again is unique! 

\begin{code}
{-@ filter :: (a -> Bool) -> xs:(UList a) -> {v:UList a | (SubElts v xs)} @-}
filter      :: (a -> Bool) -> [a] -> [a]
filter p [] = []
filter p (x:xs) 
  | p x       = x : filter p xs
  | otherwise = filter p xs
\end{code}

Unique Zipper
=============

A [zipper][http://en.wikipedia.org/wiki/Zipper_(data_structure)] is an aggregate data stucture 
that is used to arbitrary traverse the structure and update its contents.
We define a zipper as a data type that contains 
an element (called `focus`) that we are currently using,
a list of elements (called `up`) before the current one,
and a list of elements (called `down`) after the current one.

\begin{code}
data Zipper a = Zipper { focus :: a       -- focused element in this set
                       , up    :: [a]     -- elements to the left
                       , down  :: [a] }   -- elements to the right
\end{code}


We would like to state that all the values in the zipper 
are unique.
To start with, we would like to refine the `Zipper` data declaration
to express that both the lists in the structure
are unique **and** do not include `focus` in their values.

LiquidHaskell allow us to refine data type declarations, 
using the liquid comments.
So, apart from above definition definition for the `Zipper`, 
we add a refined one, stating that the data structure always enjoys 
the desired properties.

\begin{code}
{-@ 
data Zipper a = Zipper { focus :: a
                       , up    :: UListDif a focus
                       , down  :: UListDif a focus}
  @-}

{-@ type UListDif a N = {v:(UList a) | (not (ListElt N v))} @-}
\end{code}

With this annotation any time we use a `Zipper` in the code
LiquidHaskell knows that 
the `up` and `down` components are unique lists that do not include `focus`.
Moreover, when a new `Zipper` is constructed we should prove that
this property holds,
otherwise a liquid error will occur.

You may notice values inside the `Zipper` are not unique, as
a value can appear in both the `up` and the `down` components.
So, we have to specify that 
these two elements form disjoint lists.
To this end, we define two measures `getUp` and `getDown`
that return the relevant parts of the `Zipper`

\begin{code}
{-@ measure getUp :: forall a. (Zipper a) -> [a] 
    getUp (Zipper focus up down) = up
  @-}

{-@ measure getDown :: forall a. (Zipper a) -> [a] 
    getDown (Zipper focus up down) = down
  @-}
\end{code}

With these definitions, we create a type alias `UZipper` that states that 
the two list components are disjoint.

\begin{code}
{-@ type UZipper a = {v:Zipper a | (DisjointElts (getUp v) (getDown v))} @-}
\end{code}

Functions on Unique Zipper
===========================

Since we defined a unique zipper, it is straightforward for
LiquidHaskell to prove that
operations on zippers preserve uniqueness.

We can prove that a zipper that contains elements 
from a unique list is indeed unique.

\begin{code}
{-@ differentiate :: UList a -> Maybe (UZipper a) @-}
differentiate :: [a] -> Maybe (Zipper a)
differentiate []     = Nothing
differentiate (x:xs) = Just $ Zipper x [] xs
\end{code}

And vice versa, all elements of a unique zipper 
can construct a unique list.

\begin{code}
{-@ integrate :: UZipper a -> UList a @-}
integrate :: Zipper a -> [a]
integrate (Zipper x l r) = reverse l ++ x : r
\end{code}

By the definition of `UZipper` we know that `l` is a unique list
and that `x` is not an element of `l`.
Thus, if `l` is reversed using the descriptive type of `reverse` 
that we provided before, it preserves both these properties.
The append operator also uses the 
type that we show before. So LiquidHaskell, can prove that `x : r`
is indeed a unique list with elements disjoint from `reverse l` and so we can append it to `reverse l` 
and get a unique list.


With the exact same reasoning, 
we use the above list operations to create more zipper operations.

So we can reverse a unique zipper
\begin{code}
{-@ reverseZipper :: UZipper a -> UZipper a @-}
reverseZipper :: Zipper a -> Zipper a
reverseZipper (Zipper t ls rs) = Zipper t rs ls
\end{code}


More the focus up or down
\begin{code}
{-@ focusUp, focusDown :: UZipper a -> UZipper a @-}
focusUp, focusDown :: Zipper a -> Zipper a
focusUp (Zipper t [] rs)     = Zipper x xs [] where (x:xs) = reverse (t:rs)
focusUp (Zipper t (l:ls) rs) = Zipper l ls (t:rs)

focusDown = reverseZipper . focusUp . reverseZipper

{-@ q :: x:a ->  {v:[a] |(not (Set_mem x (listElts v)))} @-}
q :: a -> [a]
q _ = []
\end{code}

Finally, using the filter operation on lists
allows LiquidHaskell to prove that filtering a zipper 
also preserves uniqueness.
\begin{code}
{-@ filterZipper :: (a -> Bool) -> UZipper a -> Maybe (UZipper a) @-}
filterZipper :: (a -> Bool) -> Zipper a -> Maybe (Zipper a)
filterZipper p (Zipper f ls rs) = case filter p (f:rs) of
    f':rs' -> Just $ Zipper f' (filter p ls) rs'    -- maybe move focus down
    []     -> case filter p ls of                  -- filter back up
                    f':ls' -> Just $ Zipper f' ls' [] -- else up
                    []     -> Nothing
\end{code}

Conclusion
==========

That's all for now!
This post illustrated

- How we can use set theory to express properties the values of the list,
such as list uniqueness.
- How we can use LuquidHaskell to prove that these properties are preserved through list operations.
- How we can embed this properties in complicated data structures that use lists, such as a zipper.



