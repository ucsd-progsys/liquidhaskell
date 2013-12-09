---
layout: post
title: "Measuring the size of Structures"
date: 2013-12-22 16:12
comments: false
external-url:
categories: termination, measures
author: Niki Vazou
published: false
demo: TheSizeOfStructures.hs
---

In the [previous][ref-termination] [two][ref-lexicographic] posts we saw how refinements can be used to prove
termination. 
In both posts functions recurse on integers.
In Haskell the most common type of recursion is over recursive data structures.

Today lets see how to prove termination on functions defined over
recursive data structures.

<!-- more -->

\begin{code}
module TheSizeOfStructures where

import Prelude hiding (map)
\end{code}

Does list map Terminate?
------------------------

Lets define a `List` structure

\begin{code}
infixr `C`
data List a = N | C a (List a)
\end{code}

and a map function `lmap` on it

\begin{code}
lmap              :: (a -> b) -> (List a) -> (List b)
lmap _ N          = N
lmap f (x `C` xs) = f x `C` lmap f xs
\end{code}

Does `lmap` terminate?

At each iteration `lmap` is called with the tail of the input list.
So, the *length* of the list is decreasing at each iteration
and 
if the input list is finite, its length will reach `0` and `lmap` will terminate.

Since the length of the list is a natural number, it is
a *well-founded metric*.

From the [previous][ref-lexicographic] [two][ref-termination] posts a
well-founded metric that decreases at each iteration is all
liquidHaskell needs to prove termination on a recursive function.

Two things are left to do: teach liquidHaskell to

1. compute the length of a List

2. use this length as the decreasing metric that decreases in `lmap`.


Express Termination Metric
--------------------------

First things first,
we need to teach liquidHaskell to compute the length of the list.

Remember *measures*?
They were introduced in a [previous][ref-measure] post and in short measures
provide a mechanism to define auxiliary properties on data
values.

Now we can define a measure `llen` than maps a list to its length:
\begin{code}
{-@ measure llen  :: (List a) -> Int
    llen (N)      = 0
    llen (C x xs) = 1 + (llen xs)
  @-}
\end{code}


and then, inform liquidHaskell that this measure is *well-formed*, ie., cannot
be negative:

\begin{code}
{-@ invariant {v:(List a) | (llen v) >= 0}@-}
\end{code}


Relate List with its length
---------------------------

The final step towards verification of `lmap`'s termination is to relate the List
structure with its length `llen`.
We can do this with the usual `data` annotation

\begin{code}
{-@ data List [llen] @-}
\end{code}

that informs the tool that `llen` measures the size of a list. 
So each time the termination checker checks if a list is decreasing, it
checks if its *default* size `llen` decreases. 


Choosing the correct argument
-----------------------------

To prove termination liquidHaskell chooses one argument and tries to prove that
is decreasing.
But which argument? 
It chooses the first one for which decreasing information exists.
We have that for an integer to decrease its value should decrease 
and we specified that a list decreases if its length `llen` decreases.

In `lmap` there is no decreasing information for the function `f`, 
so liquidHaskell will correclty guess that the list argument (ie., the second
argument) should be
decreasing.

In a function that many arguments with decreasing information exist,
liquidHaskell will na&#239;vely choose the first one.

As an example, the following `posSum` function could not be proven to terminate
without our `Decrease` hint.

\begin{code}
{-@ Decrease posSum 2 @-}
posSum                            :: Int -> (List Int) -> Int
posSum acc N                      = acc
posSum acc (x `C` xs) | x > 0     = posSum (acc + x) xs
                      | otherwise = posSum (acc)     xs
\end{code}

Standard lists
--------------
You may think that all this is much work to prove that a function on a recursive
structure is terminating.
You have to both define the size of the structure and relate it with the
structure.
The good news is that this work is just performed once!

Even better, for structures like standard lists liquidHaskell has done all this
work for you!


\begin{code} The standard list `[a]` comes with the build in measure 'len', defined as
 measure len :: [a] -> Int
 len ([])   = 1
 len (x:xs) = 1 + (len xs)
\end{code}

Thus liquidHaskell will just prove that functions recursive on standard lists
shall terminate:

\begin{code}
map          :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs
\end{code}

Today we shaw how to prove termination on functions recursive over a data
structure.
You need to 

1. define the size of the structure

2. associate this size with the structure.

In the next post, 
we shall see our final mechanism to prove termination: *decreasing expressions*
Stay tuned!

[ref-measure]:       /blog/2013/01/31/sately-catching-a-list-by-its-tails.lhs/
[ref-lies]:          /blog/2013/11/23/telling-lies.lhs/ 
[ref-bottom]:        /blog/2013/12/01/getting-to-the-bottom.lhs/
[ref-termination]:   /blog/2013/12/08/termination-checking.lhs/
[ref-lexicographic]: /blog/2013/12/15/lexicographic-termination.lhs/
