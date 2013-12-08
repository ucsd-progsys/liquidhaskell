---
layout: post
title: "Termination Checking III : Measuring the size of Structures"
date: 2013-12-22 16:12
comments: true
external-url:
categories: termination, measures
author: Niki Vazou
published: true
demo: Termination3.hs
---

[Previously][ref-termination] we saw how refinements can be used to prove termination
and we promised to extend our termination checker to handle "real-word" programs.

Keeping our promise, today we shall see a trick that allows liquidHaskell to prove termination on
more recursive functions, namely *lexicographic termination*.

<!-- more -->

\begin{code}
module TheSizeOfStructures where

import Prelude hiding (map)
\end{code}

Does tree map Terminate?
------------------------

Lets define a `Tree` structure

\begin{code}
data Tree a = Leaf | Node a (Tree a) (Tree a)
\end{code}

and a map function `tmap` on it

\begin{code}
tmap                  :: (a -> b) -> (Tree a) -> (Tree b)
tmap _ Leaf           = Leaf
tmap f (Node x tl tr) = Node (f x) (tmap f tl) (tmap f tr)
\end{code}

Does `tmap` terminate?

At each iteration `tmap` is called with the left and right subtrees.
So, the *size* of the tree is decreasing at each iteration
and 
if the input tree is finite, `tmap` terminates.

Since the size of the tree is a natural number, it is
a *well-founded metric*.

From the [previous][ref-lexicographic] [two][ref-termination] posts a
well-founded metric that decreases at each iteration is all
liquidHaskell needs to prove termination on a recursive function.

Two things are left to do: teach liquidHaskell to

1. compute the size of a tree

2. use this size as the decreasing metric that decreases in `tmap`.


Express Termination Metric
--------------------------

First things first,
we need to teach liquidHaskell to compute the size of a tree.

Remember *measures*?
They were introduced in a [previous][ref-measure] post and in short measures
provide a mechanism to define auxiliary properties on data
values.

Now we can define a measure `tsize` than maps a tree to its size:
\begin{code}
{-@ measure tsize :: (Tree a) -> Int
    tsize (Leaf)         = 0
    tsize (Node x tl tr) = 1 + (tsize tl) + (tsize tr)
  @-}
\end{code}


and then, inform liquidHaskell that this measure is *well-formed*, ie., cannot
be negative:

\begin{code}
{-@ invariant {v:(Tree a) | (tsize v) >= 0}@-}
\end{code}


Relate Tree with its size
-------------------------

The final step towards verification of `tmap` termination is to relate the tree
structure with its size `tsize`.
We can do this with the usual `data` annotation

\begin{code}
{-@ data Tree [tsize] @-}
\end{code}

that informs the tool that `tsize` measures the size of a tree. 
So each time the termination checker aims to check if a tree is decreasing, it
will use the *default* size `tsize`. 



Choosing the correct argument
-----------------------------

To prove termination liquidHaskell chooses one argument and tries to prove that
is decreasing.
But which argument? 
It choosed the first one for which decreasing information exists.
We have that for an integer to decrease its value should decrease, 
and we specified that a tree decreases if its `tsize` decreases.

In `tmap` there is no decreasing information for the function `f`, 
so liquidHaskell will correclty guess that the tree argument should be
decreasing.

In a function that many arguments with decreasing information exist,
liquidHaskell will na&#239;vely choose the first one

\begin{code}
{-@ Decrease foo 2 @-}
foo              :: Int -> (Tree Int) -> Int
foo acc Leaf                       = acc
foo acc (Node x tl tr) | x > 0     = foo (acc + foo 0 tr + x) tl
                       | otherwise = foo (acc + foo 0 tr    ) tl
\end{code}

Standard lists
--------------
You may think that all this is much work to prove that a function on a recursive
structure is terminating.
You have to both define the size of the structure and relate it with the
structure.
The good news is that this work is just performed once!

Even better, structures like standard lists come with this information.


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

[ref-measures]:      /blog/2013/01/31/sately-catching-a-list-by-its-tails.lhs/
[ref-lies]:          /blog/2013/11/23/telling-lies.lhs/ 
[ref-bottom]:        /blog/2013/12/01/getting-to-the-bottom.lhs/
[ref-termination]:   /blog/2013/12/08/termination-checking-1.lhs/
[ref-lexicographic]: /blog/2013/12/15/termination-checking-2.lhs/
