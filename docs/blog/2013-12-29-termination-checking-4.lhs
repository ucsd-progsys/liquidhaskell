---
layout: post
title: "Termination Checking IV : Decreasing Expressions"
date: 2013-12-29 16:12
comments: true
external-url:
categories: termination, measures
author: Niki Vazou
published: true
demo: Termination4.hs
---

So far we proved that many recursive functions terminate.
All the functions we used share a characteristic.
They had (a list of) arguments that were (lexicographically) decreasing.

But what if no argument decreases?
An argument `i` may increase up to a higher value `hi`.
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

Does `range` terminate?
Well, 
the recursive call happens only if `lo < hi`
when `range` is called with `lo+1` and `hi`.

We can prove `range` terminating by induction on 
the quantity `D = hi - lo` 

1. If `D = hi - lo <= 0` `range` returns `0`

2. Otherwise, `range` recursively calls itself with a smaller 
`D = hi - (lo + 1)`.


That is, we have shown that at each iteration `hi - lo` 
is a *well-founded metric* that decreases.
But, [previously][ref-termination] we discussed that this is exactly what 
liquidHaksell needs to prove termination.
So, the only thing left to do is to specify this metric.

LiquidHaskell supports *decreasing expressions*, 
a mechanism to annotate the type of a recursive function
with the metric that decreases at each iteration. Thus

\begin{code}
{-@ range :: lo:Int -> hi:Int -> [Int] / [(hi - lo)] @-}
\end{code}

makes haskell 

- prove that `hi - lo` is a non-negative quantily that decreases at
each iteration, 

- or fail with a termination check error. 

title two
---------
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
Using liquidHaskell's build in [measure][ref-measure] `len`, you can specify 
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
{-@ type SL a = [a]<{\xx vv -> xx <= vv}> @-}
\end{code}

With this, all we need to prove that sortedness is preserved is to type `merge`
as
\begin{code}
{-@ merge :: Ord a => xs:(SL a) -> ys:(SL a) -> (SL a) / [(len xs) + (len ys)] @-}
\end{code}


Wrapping Up Termination Checking
--------------------------------

In the last couple of posts, we presented the mechanisms liquidHaskell uses to
prove termination

- We saw simple recursive functions, where recursion occured on a natural namber
  `i` that served as a well founded metric that proves termination

- Then we used lexicographic ordering to prove termination on functions where
  the decreasing metric constists of a list of arguments

- We saw how to handle recursion on data structures, by defining the size of
  this structure, and

- Today we saw how to express more complicated decreasing metrics.

Obviously liquidHaskell does not solve the halting problem: there do exist
terminating functions that cannot be proven terminating.
Worse, there do exist some cases of non-terminating functions tha fool
liquidHaskell: 
for instance, you can trick the tool 
if you encode termination via [recursive types][ref-rec] or [references][ref-ref], but
we aim to address such cases soon.

We claim that these mechanisms suffice to prove 
termination on numerous functions.
To support this claim, we will soon present how to use them to prove termination
on *mutually recursive* functions!



[ref-ref]
[ref-rec]:          http://en.wikipedia.org/wiki/Fixed-point_combinator#Example_of_encoding_via_recursive_types 
[ref-lies]:        /blog/2013/11/23/telling-lies.lhs/ 
[ref-bottom]:      /blog/2013/12/01/getting-to-the-bottom.lhs/
[ref-termination]: /blog/2013/12/08/termination-checking-1.lhs/
