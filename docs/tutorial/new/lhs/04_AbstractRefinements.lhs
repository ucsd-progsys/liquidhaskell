 {#abstractrefinements}
=======================

Abstracting Over Refinements
----------------------------

<div class="hidden">

\begin{code}
module AbstractRefinements where

import Prelude hiding (max)
import Language.Haskell.Liquid.Prelude
{-@ LIQUID "--no-termination" @-}
\end{code}

</div>

Abstracting Over Refinements
============================

Two Problems
------------

<div class="fragment">
**Problem 1:** 

How do we specify *both* [increasing and decreasing lists](http://web.cecs.pdx.edu/~sheard/Code/QSort.html)?</div>
</div>

<div class="fragment">
**Problem 2:** 

How do we specify *iteration-dependence* in higher-order functions?
</div>


<!--
Refined Data Constructors
-------------------------

**Example:** Increasing Lists, with strengthened constructors:

\begin{code} <br>
data L a where
  N :: L a
  C :: x:a -> xs: L {v:a | x <= v} -> L a
\end{code}

<br>

<div class="fragment">**Problem:** What if we need *both* [increasing and decreasing lists](http://web.cecs.pdx.edu/~sheard/Code/QSort.html)?</div>

-->

Problem Is Pervasive
--------------------

Lets distill it to a simple example.


Example: `maxInt` 
-----------------

`maxInt` returns the larger of two `Int`s:

\begin{code} <br> 
maxInt  :: Int -> Int -> Int 
max x y = if y <= x then x else y
\end{code}

<br>

We can give `maxInt` *many* incomparable types...

\begin{code}<br>
maxInt :: Nat -> Nat -> Nat

maxInt :: Even -> Even -> Even

maxInt :: Prime -> Prime -> Prime
\end{code}

<br>

But which is the *right* one?


Example: `maxPoly` 
------------------

\begin{code} We can instantiate `a` with `Odd`
max     :: Odd -> Odd -> Odd

maxOdd :: Odd
maxOdd = max 3 7
\end{code}


Polymorphic Max in Haskell
--------------------------

\begin{code} In Haskell the type of max is
max     :: Ord a => a -> a -> a
\end{code}


<br>

We could **ignore** the class constraints, and procced as before:

\begin{code} Instantiate `a` with `Odd`
max    :: Odd -> Odd -> Odd

maxOdd :: Odd
maxOdd = max 3 7
\end{code}


Polymorphic Add in Haskell
-----------------------

\begin{code} But this can lead to **unsoundness**:
max     :: Ord a => a -> a -> a
(+)     :: Num a => a -> a -> a
\end{code}

<br>

So, **ignoring** class constraints allows us to: 
\begin{code} instantiate `a` with `Odd`
(+)     :: Odd -> Odd -> Odd

addOdd :: Odd
addOdd = 3 + 7
\end{code}


Polymorphism via Parametric Invariants 
--------------------------------------

`max` returns *one of* its two inputs `x` and `y`. 

- **If** *both inputs* satisfy a property  

- **Then** *output* must satisfy that property

This holds, **regardless of what that property was!**
 
- That  is, we can **abstract over refinements**

- Or,  **parameterize** a type over its refinements.

Parametric Invariants
--------------------- 

\begin{code}
{-@ max :: forall <p :: a -> Prop>. Ord a => a<p> -> a<p> -> a<p> @-}
max     :: Ord a => a -> a -> a
max x y = if x <= y then y else x 
\end{code}



Where

- `a<p>` is just an abbreviation for `{v:a | (p v)}`


This type states explicitly:

- **For any property** `p`, that is a property of `a`, 

- `max` takes two **inputs** of which satisfy `p`,

- `max` returns an **output** that satisfies `p`. 



Using Abstract Refinements
--------------------------

- **If** we call `max` with two arguments with the same concrete refinement,

- **Then** the `p` will be instantiated with that concrete refinement,

- **The output** of the call will also enjoy the concrete refinement.


\begin{code}
{-@ type Odd = {v:Int | (v mod 2) = 1} @-}

{-@ maxOdd :: Odd @-}
maxOdd     :: Int
maxOdd     = max 3 5
\end{code}
