---
layout: post
title: Polymorphic Perplexion
date: 2020-04-12
comments: true
author: Ranjit Jhala 
published: true
tags: basic
demo: Insert.hs
---

Polymorphism plays a vital role in automating verification in LH.
However, thanks to its ubiquity, we often take it for granted, and 
it can be quite baffling to figure out why verification fails with 
monomorphic signatures. Let me explain why, using a simple example 
that has puzzled me and other users several times.

<!-- more -->

<div class="hidden">
\begin{code}

module PolymorphicPerplexion where
\end{code}
</div>

A Type for Ordered Lists
------------------------

[Previously](https://ucsd-progsys.github.io/liquidhaskell-blog/2013/07/29/putting-things-in-order.lhs/) 
we have seen how you can use LH to define a type of lists whose values are in increasing 
(ok, non-decreasing!) order.

First, we define an `IncList a` type, with `Emp` ("empty") 
and `:<` ("cons") constructors.

\begin{code}
data IncList a = Emp
               | (:<) { hd :: a, tl :: IncList a }

infixr 9 :<
\end{code}

Next, we refine the type to specify that each "cons" `:<`
constructor takes as input a `hd` and a `tl` which must 
be an `IncList a` of values `v` each of which is greater 
than `hd`. 

\begin{code}
{-@ data IncList a = Emp 
                   | (:<) { hd :: a, tl :: IncList {v:a | hd <= v}}  
  @-}
\end{code}

We can confirm that the above definition ensures that the only 
*legal* values are increasingly ordered lists, as LH accepts
the first list below, but rejects the second where the elements
are out of order.

\begin{code}
legalList :: IncList Int
legalList = 0 :< 1 :< 2 :< 3 :< Emp

illegalList :: IncList Int 
illegalList = 0 :< 1 :< 3 :< 2 :< Emp
\end{code}

A Polymorphic Insertion Sort
----------------------------

Next, lets write a simple *insertion-sort* function that 
takes a plain unordered list of `[a]` and returns the elements 
in increasing order:

\begin{code}
insertSortP :: (Ord a) => [a] -> IncList a
insertSortP xs = foldr insertP Emp xs

insertP             :: (Ord a) => a -> IncList a -> IncList a
insertP y Emp       = y :< Emp
insertP y (x :< xs)
  | y <= x         = y :< x :< xs
  | otherwise      = x :< insertP y xs
\end{code}

Happily, LH is able to verify the above code without any trouble!
(If that seemed too easy, don't worry: if you mess up the comparison, 
e.g. change the guard to `x <= y` LH will complain about it.)


A Monomorphic Insertion Sort
----------------------------

However, lets take the *exact* same code as above *but* change 
the type signatures to make the functions *monomorphic*, here, 
specialized to `Int` lists.

\begin{code}
insertSortM :: [Int] -> IncList Int 
insertSortM xs = foldr insertM Emp xs

insertM            :: Int -> IncList Int -> IncList Int 
insertM y Emp      = y :< Emp
insertM y (x :< xs)
  | y <= x         = y :< x :< xs
  | otherwise      = x :< insertM y xs
\end{code}

Huh? Now LH appears to be unhappy with the code! How is this possible?

Lets look at the type error:

\begin{spec}
 /Users/rjhala/PerplexingPolymorphicProperties.lhs:80:27-38: Error: Liquid Type Mismatch
  
 80 |   | otherwise      = x :< insertM y xs
                                ^^^^^^^^^^^^
   Inferred type
     VV : Int
  
   not a subtype of Required type
     VV : {VV : Int | x <= VV}
  
   In Context
     x : Int
\end{spec}

LH *expects* that since we're using the "cons" operator `:<` the "tail"
value `insertM y xs` must contain values `VV` that are greater than the 
"head" `x`. The error says that, LH cannot prove this requirement of 
*actual* list `insertM y xs`.

Hmm, well thats a puzzler. Two questions that should come to mind.

1. *Why* does the above fact hold in the first place? 

2. *How* is LH able to deduce this fact with the *polymorphic* signature but not the monomorphic one?

Lets ponder the first question: why *is* every element 
of `insert y xs` in fact larger than `x`? For three reasons:

(a) every element in `xs` is larger than `x`, as the 
    list `x :< xs` was ordered, 

(b) `y` is larger than `x` as established by the `otherwise` and crucially

(c) the elements returned by `insert y xs` are either `y` or from `xs`!

Now onto the second question: how *does* LH verify the polymorphic code,
but not the monomorphic one? The reason is the fact (c)! LH is a *modular*
verifier, meaning that the *only* information that it has about the behavior
of `insert` at a call-site is the information captured in the (refinement) 
*type specification* for `insert`. The *polymorphic* signature:

\begin{spec}
insertP :: (Ord a) => a -> IncList a -> IncList a
\end{spec}

via *parametricity*, implicitly states fact (c). That is, if at a call-site 
`insertP y xs` we pass in a value that is greater an `x` and a list of values 
greater than `x` then via *polymorphic instantiation* at the call-site, LH 
infers that the returned value must also be a list of elements greater than `x`!

However, the *monomorphic* signature 

\begin{spec}
insertM :: Int -> IncList Int -> IncList Int 
\end{spec}

offers no such insight. It simply says the function takes in an `Int` and another 
ordered list of `Int` and returns another ordered list, whose actual elements could 
be arbitrary `Int`. Specifically, at the call-site `insertP y xs` LH has no way to 
conclude the the returned elements are indeed greater than `x` and hence rejects 
the monomorphic code.


Perplexity
----------

While parametricity is all very nice, and LH's polymorphic instanatiation is very 
clever and useful, it can also be quite mysterious. For example, q curious user 
Oisín [pointed out](https://github.com/ucsd-progsys/liquidhaskell-tutorial/issues/91) 
that while the code below is *rejected* that if you *uncomment* the type signature 
for `go` then it is *accepted* by LH!

\begin{code}
insertSortP' :: (Ord a) => [a] -> IncList a 
insertSortP' = foldr go Emp 
  where
    -- go :: (Ord a) => a -> IncList a -> IncList a
    go y Emp       = y :< Emp
    go y (x :< xs)
      | y <= x     = y :< x :< xs
      | otherwise  = x :< go y xs
\end{code}

This is thoroughly perplexing, but again, is explained by the absence of 
parametricity. When we *remove* the type signature, GHC defaults to giving 
`go` a *monomorphic* signature where the `a` is not universally quantified, 
and which roughly captures the same specification as the monomorphic `insertM` 
above causing verification to fail! 

Restoring the signature provides LH with the polymorphic specification, 
which can be instantiated at the call-site to recover the fact `(c)` 
that is crucial for verification.


Moral
-----

I hope that example illustrates two points.

First, *parametric polymorphism* lets type specifications 
say a lot more than they immediately let on: so do write 
polymorphic signatures whenever possible.

Second, on a less happy note, *explaining* why fancy type 
checkers fail remains a vexing problem, whose difficulty 
is compounded by increasing the cleverness of the type 
system. 

We'd love to hear any ideas you might have to solve the 
explanation problem!
