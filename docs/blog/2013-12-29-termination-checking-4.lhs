---
layout: post
title: "Termination Checking IV : Decreasing Expressions"
date: 2013-12-29 16:12
comments: true
external-url:
categories: termination, measures
author: Niki Vazou
published: false
demo: DecreasingExpressions.hs
---

So far we proved that many recursive functions terminate.
All the functions we used share a characteristic.
They had (a list of) arguments that were (lexicographically) decreasing.

What if no argument decreases?
Consider an argument `i` that increases up to a higher value `hi`.
As `i` increases the difference `hi - i` decreases and will eventually reach
`0`.
This difference "witnesses" termination.

Today we will describe 
the last mechanism liquidHaskell uses to prove termination:
*decreasing expressions*
that allow us to annotate functions with termination withnesses.

<!-- more -->

\begin{code}
module DecreasingExpressions where

range ::          Int -> Int -> [Int]
merge :: Ord a => [a] -> [a] -> [a]
\end{code}

Termination on Increasing Arguments
-----------------------------------

Consider a `range` function that takes two integers 
a `lo`wer and a `hi`gher and returns the list `[lo, lo+1, ..., hi-1]`

\begin{code}
range lo hi | lo < hi   = lo : range (lo + 1) hi
            | otherwise = []
\end{code}

Clearly the difference `hi - lo` is decreasing at each iteration and will
eventually reach `0`.
That is, `hi - lo` is a *well-founded metric* that decreases.
[Previously][ref-termination] we discussed that this is exactly what 
liquidHaksell needs to prove termination.

Sadly, liquidHaskell cannot synthesize this metric.
But provides a mechanism for the user to specify it.
With *decreasing expressions*, 
we can annotate the type of a recursive function
with the termination witness. Thus

\begin{code}
{-@ range :: lo:Int -> hi:Int -> [Int] / [(hi - lo)] @-}
\end{code}

makes liquidHaskell 
prove that `hi - lo` is a non-negative quantily that decreases at
each iteration, 

Termination on a Function of the Arguments
------------------------------------------

Lets illustrate the power of decreasing expressions with a more involved
example.

Consider the standard `merge` from the homonymous sorting function 

\begin{code}
merge (x:xs) (y:ys) 
  | x < y     = x : merge xs     (y:ys)
  | otherwise = y : merge (x:xs) ys
\end{code}

Does `merge` terminate?
Well it does because at each iteration the sum of the lengths of the two
arguments decreases. 
Using liquidHaskell's build in [measure][ref-measure] `len`
to get the length of a list, we can specify 
`(len xs) + (len ys)`
as the decreasing expression for `merge`

\begin{code}_
{-@ merge :: Ord a => xs:[a] -> ys:[a] -> [a] / [(len xs) + (len ys)] @-}
\end{code}


By the way, the power of liquidHaskell does not stop at proving `merge`
terminating. 
It extends to proving that given two sorted lists, `merge` will actually return
a sorted list!

[Some time ago][ref-slist], we represented Sorted Lists as
\begin{code}
{-@ type SL a = [a]<{\x v -> x <= v}> @-}
\end{code}

With this, all we need to prove that sortedness is preserved is to type `merge`
as
\begin{code}
{-@ merge :: Ord a => xs:(SL a) -> ys:(SL a) -> (SL a) 
           / [(len xs) + (len ys)]                                    @-}
\end{code}


Wrapping Up Termination Checking
--------------------------------

In the last couple of posts, we presented the mechanisms liquidHaskell uses to
prove termination

- We [started][ref-termination] with functions recursive on some natural namber
  `i` that served as a decreasing metric to prove termination.

- [Then][ref-lex], we used lexicographic ordering to prove termination on functions where
  the decreasing metric constists of a list of arguments.

- [After][ref-structures], we saw how to handle recursion on data structures: by proving the size of
  this structure is decreasing, and

- Today, we saw how to express more complicated decreasing metrics.

Obviously liquidHaskell does not solve the halting problem: there do exist
terminating functions that cannot be proven terminating.
Worse, there do exist some cases of non-terminating functions tha fool
liquidHaskell: 
for instance, you can trick the tool 
if you encode termination via [recursive types][ref-rec] or
[references][ref-ref].
We aim to soon address such corner cases.

We claim that the above mechanisms suffice to prove 
termination on numerous functions.
Even *mutually recursive* ones, as we shall soon see.



[ref-ref]:          https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/todo/Recursion1.hs
[ref-rec]:          http://en.wikipedia.org/wiki/Fixed-point_combinator#Example_of_encoding_via_recursive_types 
[ref-lies]:        /blog/2013/11/23/telling-lies.lhs/ 
[ref-bottom]:      /blog/2013/12/01/getting-to-the-bottom.lhs/
[ref-termination]: /blog/2013/12/08/termination-checking.lhs/
[ref-lex]:         /blog/2013/12/15/termination-checking-2.lhs/
[ref-structures]:  /blog/2013/12/22/termination-checking-3.lhs/
[ref-measure]:     /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/
[ref-slist]:       /blog/2013/07/29/putting-things-in-order.lhs/
