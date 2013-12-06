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
\end{code}

Does tree map Terminate?
------------------------

Lets define a `Tree` structure

\begin{code}
data Tree a = Leaf | Node a (Tree a) (Tree a)
\end{code}

and a map function on it

\begin{code}
tmap              :: (a -> b) -> (Tree a) -> (Tree b)
tmap _ Leaf           = Leaf
tmap f (Node x tl tr) = Node (f x) (tmap f tl) (tmap f tr)
\end{code}

Does `tmap` terminate?

At each iteration `tmap` is called with the left and right subtrees of the input list.
So, the size of the tree is decreasing at each iteration
and 
if the input tree is finite, `tmap` terminates.

Since the size of the tree is a natural number, it is
a *well-founded metric*.

From the [previous][ref-lexicographic] [two][ref-termination] posts a
well-founded metric that decreases at each iteration is all
liquidHaskell needs to prove termination on a recursive function.

Two things are left to do: teach liquidHaskell to

1. compute the size of a tree

2. use this size to size trees.


Express Termination Metric
--------------------------

First things first,
we need to teach liquidHaskell to compute the size of a tree.

Remember *measures*?
They were introduced in a [previous][ref-measure] post and in short measures
provide a mechanism to define auxiliary (or so-called ghost) properties on data
values.

Now we can define a measure `tlen` than maps a trees to its size:
\begin{code}
{-@ measure tlen :: (Tree a) -> Int
    tlen (Leaf)         = 0
    tlen (Node x tl tr) = 1 + (tlen tl) + (tlen tr)
  @-}
\end{code}


and then, inform liquidHaskell that this measure is *well-formed*, ie., cannot
be negative:

\begin{code}
{-@ invariant {v:(Tree a) | (tlen v) >= 0}@-}
\end{code}


Relate list with its size
-------------------------

The final step towards verification of termination is to relate the tree
structure with its size `tlen`.
We can do this with the usual `data` annotation

\begin{code}
{-@ data Tree [tlen] @-}
\end{code}

that informs the tool that `tlen` measures the size of a tree. 
So each time the termination checker wishes to check if a tree is decreasing, it
will use the *default* size `tlen`. 



Choosing the correct argument
-----------------------------

To prove termination liquidHaskell chooses one argument and tries to prove that
is decreasing.
But which argument? 
It choosed the first one for which decreasing information exists.
We know that for an integer to decrease, its value should decrease, 
and we specified that a tree decreases if its `tlen` decreases.

In `tmap` there is no decreasing information for the function `f`, 
this liquidHaskell will correclty guess that the tree argument should be
decreasing.

In a function that many arguments with decreasing information exist,
liquidHaskell will va&#239;vely choose the first one

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
You have 1. to define the size of the structure and relate it with the
structure.
The good news is that this work is just performed once!

Even better, structures like standard lists come with this information.


\begin{code} The list `[a]` comes with the build in measure 'len', defined as
 measure len :: [a] -> Int
 len ([])   = 1
 len (x:xs) = 1 + (len xs)
\end{code}

Thus liquidHaskell will just prove that functions recursive on standard lists
shall terminate:

\begin{code}
mymap          :: (a -> b) -> [a] -> [b]
mymap _ []     = []
mymap f (x:xs) = f x : mymap f xs
\end{code}

Today we shaw how to prove termination on functions recursive over a data
structure.
You need to 

1. define the size of the structure

2. associate this size with the structure.

In the next post, 
we shall see our final mechanism to prove termination: *decreasing expressions*
Stay tuned!

Using a Different Size
----------------------

Suppose that our tree is a Binary Seach Tree and we would like to `insert` a
value in it

\begin{code}
insert :: Ord a => a -> Tree a -> Tree a
insert x Leaf = Node x Leaf Leaf
insert x (Node y tl tr) | x == y     = Node x tl tr
                        | x > y      = Node y tl (insert x tr)
                        | otherwise  = Node y (insert x tl) tr
\end{code}

LiquidHaskell can happily verify that at each iteration `tlen` decreases, so
`insert` does terminate.

But `tlen` is such an overaproximation of the decreasing metric.
We can get more strict and define a "logarithmic" size on trees:
\begin{code}
{-@ measure ltlen :: (Tree a) -> Int
    ltlen (Leaf) = 0
    ltlen (Node x tl tr) = 1 + (max (ltlen tl) (ltlen tr))
  @-}

{-@ invariant {v:(Tree a) | (ltlen v) >= 0} @-}
\end{code}


Now, `insert` will typecheck against the signature
\begin{code}
{-@ insert :: Ord a => x:a -> t:(Tree a) -> Tree a / [(ltlen t)] @-}
\end{code}

that specifies that the decreasing metric 

In this example we used a *decreasing* expression to get a more precise
termination metric.
In the next post we will see how decreasing expression can express more
compicated metrics.


Today we shaw how to prove termination on functions recursive over a data
structure.
You need to 

1. define the size of the structure

2. associate this size with the structure.

Once again we will end by stating that there exists an alternative
specification.

You may note that we don't have to specify that the second argument is
decreasing. 
So



With all these information, liquidHaskell can prove that `lmap` is recursively
called with smaller lists, ie., lists with decreasing `llen`, so it does
terminate.


[ref-lies]:        /blog/2013/11/23/telling-lies.lhs/ 
[ref-bottom]:      /blog/2013/12/01/getting-to-the-bottom.lhs/
[ref-termination]: /blog/2013/12/08/termination-checking-1.lhs/
