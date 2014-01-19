 {#abstractrefinements}
=======================


Abstract Refinements
--------------------

<div class="hidden">

\begin{code}
module AbstractRefinements where

import Prelude hiding (max)
import Language.Haskell.Liquid.Prelude
{-@ LIQUID "--no-termination" @-}

odd_and_even :: (Int, Int)
o, no        :: Int
max          :: Ord a => a -> a -> a
\end{code}

</div>

Abstract Refinements
====================

Two Problems
------------

<div class="fragment">
**Problem 1:** 

How do we specify *both* [increasing and decreasing lists](http://web.cecs.pdx.edu/~sheard/Code/QSort.html)?
</div>

<br>

<div class="fragment">
**Problem 2:** 

How do we specify *iteration-dependence* in higher-order functions?
</div>

Problem Is Pervasive
--------------------

Lets distill it to a simple example...

Example: `maxInt` 
-----------------

Compute the larger of two `Int`s:

\begin{code} <br> 
maxInt     :: Int -> Int -> Int 
maxInt x y = if y <= x then x else y
\end{code}

Example: `maxInt` 
-----------------

Hase *many incomparable* refinement types...

\begin{code}<br>
maxInt :: Nat   -> Nat   -> Nat
maxInt :: Even  -> Even  -> Even
maxInt :: Prime -> Prime -> Prime
\end{code}

<br>

<div class="fragment">Yikes. **Which** one should we use?</div>

Refinement Polymorphism 
-----------------------

`maxInt` returns *one of* its two inputs `x` and `y`. 

<div class="fragment" align="center">

<br>

---------   ---   -------------------------------------------
   **If**    :    the *inputs* satisfy a property  

 **Then**    :    the *output* satisfies that property
---------   ---   -------------------------------------------

<br>

</div>

<div class="fragment">Above holds *for all* properties!</div>

<div class="fragment"> 

<br>

**Need to abstract refinements over types**

By Type Polymorphism?
---------------------

\begin{code} <br> 
max :: α -> α -> α 
max x y = if y <= x then x else y
\end{code}

<br>

<div class="fragment">Instantiate `α` at callsites...</div>

<div class="fragment">

\begin{code}
{-@ odd_and_even :: ( Odd, Even) @-}
odd_and_even     =  ( max 3 7    -- α := Odd
                    , max 2 4 )  -- α := Even 
\end{code}

</div>

By Type Polymorphism?
---------------------

\begin{code} <br> 
max :: α -> α -> α 
max x y = if y <= x then x else y
\end{code}

<br>

But there is a fly in the ointment ...

Polymorphic `max` in Haskell
----------------------------

\begin{code} In Haskell the type of max is
max :: (Ord a) => a -> a -> a
\end{code}

<br>

We could *ignore* the class constraints, instantiate as before...

\begin{code}
{-@ o :: Odd @-}
o     = max 3 7  -- α := Odd 
\end{code}


Polymorphic `(+)` in Haskell
----------------------------

\begin{code} ... but this is *unsound*!
max     :: (Ord a) => a -> a -> a
(+)     :: (Num a) => a -> a -> a
\end{code}

<br>

<div class="fragment">

*Ignoring* class constraints would let us "prove":

\begin{code}
{-@ no :: Odd @-}
no     = 3 + 7    -- α := Odd !
\end{code}

</div>

Type Polymorphism? No.
----------------------

<div class="fragment">Need to try a bit harder...</div>

By Parametric Refinements!
--------------------------

That is, enable *quantification over refinements*...

Parametric Refinements 
----------------------

\begin{code}
{-@ max :: forall <p :: a -> Prop>. 
             Ord a => a<p> -> a<p> -> a<p> 
  @-}
max x y = if x <= y then y else x 
\end{code}

<br>


<div class="fragment">Type says: **for any** `p` that is a property of `a`, </div>

- <div class="fragment">`max` **takes** two inputs that satisfy `p`,</div>

- <div class="fragment">`max` **returns** an output that satisfies `p`.</div>

Parametric Refinements 
----------------------

\begin{code}<br> 
{-@ max :: forall <p :: a -> Prop>. 
             Ord a => a<p> -> a<p> -> a<p> 
  @-}
max x y = if x <= y then y else x 
\end{code}

<br>

[Key Insight:](http://goto.ucsd.edu/~rjhala/papers/abstract_refinement_types.html) `a<p>` is simply `{v:a|(p v)}`

<br>

<div class="fragment">Abstract Refinement is an *uninterpreted function* in SMT logic</div>

Parametric Refinements 
----------------------

\begin{code}<br> 
{-@ max :: forall <p :: a -> Prop>. 
             Ord a => a<p> -> a<p> -> a<p> 
  @-}
max x y = if x <= y then y else x 
\end{code}

<br>

**Check** and **Instantiate** type using *SMT/predicate abstraction*

HEREHERE


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
