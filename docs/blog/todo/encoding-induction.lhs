
---
layout: post
title: "Encoding Induction with Abstract Refinements"
date: 2013-02-20 16:12
comments: true
external-url:
categories: abstract-refinements 
author: Niki Vazou
published: false
---

In this example, we explain how abstract refinements allow us to formalize
some kinds of structural induction within the type system. 

\begin{code}
module Inductive where
\end{code}

Measures
--------
First, lets define an inductive data type `Vec`

\begin{code}
data Vec a = Nil | Cons a (Vec a)
\end{code}

And let us formalize a notion of _length_ for lists within the refinement logic. 

To do so, we define a special `llen` measure by structural induction

\begin{code}
{-@ measure llen     :: forall a. Vec a -> Int 
    llen (Nil)       = 0 
    llen (Cons x xs) = 1 + llen(xs)
  @-}
\end{code}


Note that the symbol `llen` is encoded as an _uninterpreted_ function in the refinement logic, and is, except for the congruence axiom, opaque to the SMT solver. The measures are guaranteed, by construction, to terminate, and so we can soundly use them as uninterpreted functions in the refinement logic. Notice also, that we can define _multiple_ measures for a type; in this case we simply conjoin the refinements from each measure when refining each data constructor.

As a warmup, lets check that a _real_ length function indeed computes the length of the list:

\begin{code}
{-@ sizeOf :: xs:Vec a -> {v: Int | v = llen(xs)} @-}
sizeOf             :: Vec a -> Int
sizeOf Nil         = 0
sizeOf (Cons _ xs) = 1 + sizeOf xs
\end{code}



With these strengthened constructor types, we can verify, for example, that `myappend` produces a list whose length is the sum of the input lists'
lengths:

\begin{code}
{-@ myappend :: l: (Vec a) -> m: (Vec a) -> {v: Vec a | llen(v)=llen(l)+llen(m)} @-}
myappend Nil         zs = zs
myappend (Cons y ys) zs = Cons y (myappend ys zs)
\end{code}


\begin{code}However, consider an alternate definition of `myappend` that uses `foldr`
myappend' ys zs = foldr (:) zs ys 
\end{code}

where `foldr :: (a -> b -> b) -> b -> [a] -> b`.
It is unclear how to give `foldr` a (first-order) refinement type that captures the rather complex fact that the fold-function is ''applied'' all over the list argument, or, that it is a catamorphism. Hence, hitherto, it has not been possible to verify the second definition of `append`.


Typing Folds
------------

Abstract refinements allow us to solve this problem with a very expressive type for _foldr_ whilst remaining firmly within the boundaries of SMT-based decidability. We write a slightly modified fold:

\begin{code}
{-@ efoldr :: forall a b <p :: x0:Vec a -> x1:b -> Prop>. 
                op:(xs:Vec a -> x:a -> b:b <p xs> -> 
                  exists [xxs : {v: Vec a | v = (Inductive.Cons x xs)}].
                     b <p xxs>) 
              -> vs:(exists [zz: {v: Vec a | v = Inductive.Nil}]. b <p zz>) 
              -> ys: Vec a
              -> b <p ys>
  @-}
efoldr :: (Vec a -> a -> b -> b) -> b -> Vec a -> b
efoldr op b Nil         = b
efoldr op b (Cons x xs) = op xs x (efoldr op b xs) 
\end{code}

The trick is simply to quantify over the relationship `p` that `efoldr` establishes between the input list `xs` and the output `b` value. This is formalized by the type signature, which encodes an induction principle for lists: 
the base value `b` must (1) satisfy the relation with the empty list, and the function `op` must take (2) a value that satisfies the relationship with the tail `xs` (we have added the `xs` as an extra "ghost" parameter to `op`), (3) a head value `x`, and return (4) a new folded value that satisfies the relationship with `x:xs`.
If all the above are met, then the value returned by `efoldr` satisfies the relation with the input list `ys`.

This scheme is not novel in itself --- what is new is the encoding, via uninterpreted predicate symbols, in an SMT-decidable refinement type system.

Using Folds
-----------

Finally, we can use the expressive type for the above `foldr` to verify various inductive properties of client functions:

\begin{code}
{-@ size :: xs:Vec a -> {v: Int | v = llen(xs)} @-}
size :: Vec a -> Int
size = efoldr (\_ _ n -> suc n) 0

{-@ suc :: x:Int -> {v: Int | v = x + 1} @-}
suc :: Int -> Int
suc x = x + 1 

{-@ 
   myappend'  :: xs: Vec a -> ys: Vec a -> {v: Vec a | llen(v) = llen(xs) + llen(ys)} 
  @-} 
myappend' xs ys = efoldr (\_ z zs -> Cons z zs) ys xs 
\end{code}


\begin{code}The verification proceeds by just (automatically) instantiating the refinement parameter `p` of `efoldr` with the concrete refinements, via Liquid typing:

{\xs v -> v = llen(xs)}                   -- for size
{\xs v -> llen(v) = llen(xs) + llen(zs)}  -- for myappend'
\end{code}

