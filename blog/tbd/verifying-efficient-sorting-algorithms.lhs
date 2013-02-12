---
layout: post
title: "Verifing Efficient Sorting Algorithms"
date: 2013-02-15 16:12
comments: true
external-url:
categories: abstract-refinements
author: Niki Vazou
published: false
---


In this example, we will see how abstract refinements can be used to verify
complex sorting algorithms, like the ones implemented in `Data.List`.

\begin{code}
module GhcSort (sort, sort1, sort2) where
\end{code}

Once again, we defined the type of sorted lists as:

\begin{code}
{-@ type SList a = [a]<{v: a | (v >= fld)}> @-}
\end{code}

and we aim to prove that all sorting functions return a list if this type.

QuickSort
---------

Prelude used to implement the below variant of quicksort, as its sorting algorithm.

First, we define `qsort`:
\begin{code}
qsort :: (Ord a) =>  a -> [a] -> [a] -> [a]
qsort _ []     r = r
qsort _ [x]    r = x:r
qsort w (x:xs) r = qpart w x xs [] [] r
\end{code}


In `qsort w ys r`, `r` is a sorted list with values greater than `w` and `ys` is a non-sorted list with values lower or equal to `w`.
If there is at most one element in `ys`, `qsort` returns the sorted list `ys++r`.
Otherwise, `ys=(x:xs)`, and to short `ys`, `qsort` choses as _pivot element_ the `x` and calls `qpart`:

\begin{code}
qpart :: (Ord a) => a -> a -> [a] -> [a] -> [a] -> [a] -> [a]
qpart w x [] rlt rge r =
    -- rlt and rge are in reverse order and must be sorted with an
    -- anti-stable sorting
    rqsort x rlt (x:rqsort w rge r)
qpart w x (y:ys) rlt rge r =
    case compare x y of
        GT -> qpart w x ys (y:rlt) rge r
        _  -> qpart w x ys rlt (y:rge) r
\end{code}

In `qpart w x xs rlt rge r`, `r` is a sorted list with values greater than `w`, all other argument lists are not sorted and their values are less or equal to `w`. Moreover, `rge` (`rlt`) has values greater or equal (less) than the pivot element `x`.
`qpart` splits `xs` values between `rlt` and `rge` and when there are no more values in `xs` it calls `qsort` on these two lists to recursively sort them.
But, since `qpart` reverses the order of equal values, it actually calls `rqsort` that behaves similar to `qsort`, apart from reversing once more the order of equal values: 

\begin{code}
-- rqsort is as qsort but anti-stable, i.e. reverses equal elements
rqsort :: (Ord a) => a -> [a] -> [a] -> [a]
rqsort _ []     r = r
rqsort _ [x]    r = x:r
rqsort w (x:xs) r = rqpart w x xs [] [] r

rqpart :: (Ord a) => a -> a -> [a] -> [a] -> [a] -> [a] -> [a]
rqpart w x [] rle rgt r =
    qsort x rle (x:qsort w rgt r)
rqpart w x (y:ys) rle rgt r =
    case compare y x of
        GT -> rqpart w x ys rle (y:rgt) r
        _  -> rqpart w x ys (y:rle) rgt r
\end{code}

Finally, to sort a list `ls` we have to call `qsort` with an empty initially sorted list. Also, we have to provide a `w` such that all elements in `ls` are less or equal to `w`. So, we have the sorting function:

\begin{code}
{-@ sort1 :: (Ord a) => w:a -> ls:[{v:a|v<=w}] -> SList a @-}
sort1 :: (Ord a) => a -> [a] -> [a]
sort1 w ls = qsort w ls []
\end{code}

We note that the `w` that appears in all functions is a ``ghost'' variable that we added so we can prove the correctness of the function. In other words, `w` is not actually used by the functions, but it is needed so that we can prove that always any value in the sorted list `r` is greater than any value in the other lists.



Mergesort
---------
In 2002, Ian Lynagh proposed that GHC should use a sorting algorithm with nlogn worst case performance, so he proposed proposed the below mergesort function:


\begin{code}
mergesort :: (Ord a) => [a] -> [a]
mergesort = mergesort' . map wrap

mergesort' :: (Ord a) => [[a]] -> [a]
mergesort' [] = []
mergesort' [xs] = xs
mergesort' xss = mergesort' (merge_pairs xss)

merge_pairs :: (Ord a) => [[a]] -> [[a]]
merge_pairs [] = []
merge_pairs [xs] = [xs]
merge_pairs (xs:ys:xss) = merge xs ys : merge_pairs xss

merge :: (Ord a) => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
 = case x `compare` y of
        GT -> y : merge (x:xs)   ys
        _  -> x : merge    xs (y:ys)

wrap :: a -> [a]
wrap x = [x]
\end{code}

This is a usual merge sort function: Initially each element of the list is wrapped in an one-element list. So, a list of sorted lists in constructed and applied to `mergesort'`. `mergesort'` is always called on list of sorted lists, so if its argument has zero or one elements it trivially returns a sorted list, otherwise it merges all consequtive pairs, with `merge_pairs`, and recursivelly calls itself. In the same way, `merge_pairs` either returns a trivially sorted list, or it merges two consequtive lists and recursivelly calls itself on the rest. Finally, two sorted lists are merged by `merge` in the expected way.


Without any code modifications, our system can prove that all invariants are kept, and ultimately `mergesort` returns a sorted list:

\begin{code}
{-@ sort2 :: (Ord a) => [a] -> SList a @-}
sort2 :: (Ord a) => [a] -> [a]
sort2 = mergesort
\end{code}


Official GHC Sort
-----------------
In 2009 `mergesort` was replaced by the bellow function, which is similar to "A smooth applicative merge sort", as proposed in 1982 by Richard O'Keefe:

First we define `descending a as bs`, that has the invariant tha all values in `as` are greater than `a` and returns a list whose first element is the greatest descending prefix list in `bs`, reversed. 

\begin{code}
descending a as (b:bs)
  | a `compare` b == GT = descending b (a:as) bs
descending a as bs      = (a:as): sequences bs
\end{code}

Then we define `ascending a as bs`, that has the invariant tha all arguments of `as` are greater than or equal to `a` and returns a list whose first element is the greatest ascending prefix list in `bs`. To avoid reversing this sublist, `as` is not a list, but a function that every time stores the beggining of the lists and expects its ending.

\begin{code}  
ascending a as (b:bs)
  | a `compare` b /= GT = ascending b (\ys -> as (a:ys)) bs
ascending a as bs       = as [a]: sequences bs
\end{code}

Since, an arbitrary list can be split in consecutive ascending or descending sublists we define the function `sequences ls` that recursively uses `ascending` and `descending` to split `ls` in these sublists.

\begin{code}
sequences (a:b:xs)
  | a `compare` b == GT = descending b [a]  xs
  | otherwise           = ascending  b (a:) xs
sequences [x] = [[x]]
sequences []  = [[]]
\end{code}

Then, we define a `mergeAll` function that merges sorted lists: 

\begin{code}
mergeAll [x] = x
mergeAll xs  = mergeAll (mergePairs xs)

mergePairs (a:b:xs) = merge a b: mergePairs xs
mergePairs [x]      = [x]
mergePairs []       = []
\end{code}

Finally, we define the sorting function that applies `mergeAll` to the result of `sequences` applied in the initial list.

\begin{code}
{-@ sort :: (Ord a) => [a] -> SList a @-}
sort :: (Ord a) => [a] -> [a]
sort = mergeAll . sequences
\end{code}

Our system can again prove that all the above invariants hold, and `sort` produces a sorted list.

We have to note that the initial ghc functions take comparing function as an argument. But to prove sortedness, we have to transfer the information we get from comparison to the type system. So we actually modified all the above code, by inlining the `compare` function instead of passing it as an argument.

