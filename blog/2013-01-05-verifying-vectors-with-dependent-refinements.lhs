
---
layout: post
title: "Verifying Vectors With Dependent Refinements"
date: 2013-01-05 16:12
author: Ranjit Jhala
published: false 
comments: true
external-url:
categories: basic
---

Hopefully, [this article](/blog/2012/12/20/refinement-types-101.lhs/) gave
you a basic idea about what refinement types look like. Today, lets build
on that intuition with a few more easy examples that

1. show how to do compile-time **bounds checking** with LiquidHaskell
2. illustrate functions with **recursion** and **data types**, and, as an added bonus, 
3. discuss how the types interact with **parametric polymorphism**.

Bounds for Vectors
------------------

One classical [use-case](http://www.cs.bu.edu/~hwxi/DML/DML.html) for 
refinement types is to verify the safety of accesses of arrays and 
vectors and such, by proving that the indices used in such accesses 
are *within bounds*. In this article, we will develop the above ideas 
by writing a few short functions that manipulate vectors, such as those
from the popular [vector](http://hackage.haskell.org/package/vector) library.


We can **specify** bounds safety by writing refined versions of the types for the 
[key functions](https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/Vector.spec) 
exported by the module `Data.Vector`. 

\begin{code} (Partial) Specifications for `Data.Vector`
module spec Data.Vector where

import GHC.Base

measure vlen    :: forall a. (Vector a) -> Int 
assume length   :: forall a. x:(Vector a) -> {v : Int | v = vlen(x)}
assume !        :: forall a. x:(Vector a) -> {v : Int | ((0 <= v) && (v < vlen(x))) } -> a 
\end{code}

In particular, we 

- *define* a **measure** called `vlen` which denotes the size of the vector,
- *assume* that the `length` function **returns** an integer equal to the vector's size, and
- *assume* that the lookup function `!` **requires** an index between `0` and the vector's size.

**Note:** We write ``assume" because in this scenario we are not actually
*verifying* the implementation of `Data.Vector`. If you wanted to do that,
you would simply ascribe the above types to the relevant functions in the
Haskell source file. Also, if you strip out the green bits (i.e. the logical
predicates) you get back *exactly* the good old Haskell types for the above 
functions.


- Data.Vector
    - create vector
    - access vector [safe]
    - access vector [unsafe]

Our First Recursive Function
----------------------------

- Vector-Abs-Sum // recursion


Bottling Recursion With a Higher-Order `loop`
---------------------------------------------

- loop           // recursion + HOF 
- dotProduct     // uses loop use HOF


Refining Data Types
--------------------

- range          // uses loop  + show LIST


Refinements and Polymorphism
----------------------------

- Vector-Abs-Sum // uses range + MAP
- argmin         // uses range + map and fold

