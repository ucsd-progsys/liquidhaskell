  {#abstractrefinements}
========================

<div class="hidden">

\begin{code}
module AbstractRefinements where

import Prelude 
import Language.Haskell.Liquid.Prelude
{-@ LIQUID "--no-termination" @-}

o, no        :: Int
maxInt       :: Int -> Int -> Int
\end{code}
</div>



Abstract Refinements
--------------------



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

<div class="fragment">

<br>

(First, a few aliases)

<br>

\begin{code}
{-@ type Odd  = {v:Int | (v mod 2) = 1} @-}
{-@ type Even = {v:Int | (v mod 2) = 0} @-}
\end{code}

</div>


Example: `maxInt` 
-----------------

Compute the larger of two `Int`s:

\begin{code} <br> 
maxInt     :: Int -> Int -> Int 
maxInt x y = if y <= x then x else y
\end{code}



Example: `maxInt` 
-----------------

Has **many incomparable** refinement types

\begin{code}<br>
maxInt :: Nat  -> Nat  -> Nat
maxInt :: Even -> Even -> Even
maxInt :: Odd  -> Odd  -> Odd 
\end{code}

<br>

<div class="fragment">Oh no! **Which** one should we use?</div>


Refinement Polymorphism 
-----------------------

`maxInt` returns *one of* its two inputs `x` and `y` 

<div align="center">

<br>

---------   ---   -------------------------------------------
   **If**    :    the *inputs* satisfy a property  

 **Then**    :    the *output* satisfies that property
---------   ---   -------------------------------------------

<br>

</div>

<div class="fragment">Above holds *for all properties*!</div>

<br>

<div class="fragment"> 

**Need to abstract properties over types**

</div>

<!--

By Type Polymorphism?
---------------------

\begin{code} <br> 
max     :: α -> α -> α 
max x y = if y <= x then x else y
\end{code}

<div class="fragment"> 

Instantiate `α` at callsites

\begin{code}
{-@ o :: Odd  @-}
o = maxInt 3 7     -- α := Odd

{-@ e :: Even @-}
e = maxInt 2 8     -- α := Even
\end{code}

</div>

By Type Polymorphism?
---------------------

\begin{code} <br> 
max     :: α -> α -> α 
max x y = if y <= x then x else y
\end{code}

<br>

But there is a fly in the ointment ...

Polymorphic `max` in Haskell
----------------------------

\begin{code} In Haskell the type of max is
max :: (Ord α) => α -> α -> α
\end{code}

<br>

\begin{code} Could *ignore* the class constraints, instantiate as before...
{-@ o :: Odd @-}
o     = max 3 7  -- α := Odd 
\end{code}


Polymorphic `(+)` in Haskell
----------------------------

\begin{code} ... but this is *unsound*!
max :: (Ord α) => α -> α -> α
(+) :: (Num α) => α -> α -> α
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

-->

Parametric Refinements
----------------------

Enable *quantification over refinements* ...

Parametric Refinements 
----------------------

\begin{code}
{-@ maxInt :: forall <p :: Int -> Prop>. 
                Int<p> -> Int<p> -> Int<p>  @-}

maxInt x y = if x <= y then y else x 
\end{code}

<br>


<div class="fragment">Type says: **for any** `p` that is a property of `Int`, </div>

<br>

- <div class="fragment">`max` **takes** two `Int`s that satisfy `p`,</div>

- <div class="fragment">`max` **returns** an `Int` that satisfies `p`.</div>

Parametric Refinements 
----------------------

\begin{code}<br>
{-@ maxInt :: forall <p :: Int -> Prop>. 
                Int<p> -> Int<p> -> Int<p>  @-}

maxInt x y = if x <= y then y else x 
\end{code}

<br>

[Key idea: ](http://goto.ucsd.edu/~rjhala/papers/abstract_refinement_types.html) &nbsp; `Int<p>`  &nbsp; is just  &nbsp; `{v:Int | (p v)}`

<br>

<div class="fragment">i.e., Abstract Refinement is an **uninterpreted function** in SMT logic</div>

Parametric Refinements 
----------------------

\begin{code}<br>
{-@ maxInt :: forall <p :: Int -> Prop>. 
                Int<p> -> Int<p> -> Int<p>  @-}

maxInt x y = if x <= y then y else x 
\end{code}

<br>

**Check** and **Instantiate** refinements using *SMT & predicate abstraction*

Using Abstract Refinements
--------------------------

- <div class="fragment">**When** we call `maxInt` with args with some refinement,</div>

- <div class="fragment">**Then** `p` instantiated with *same* refinement,</div>

- <div class="fragment">**Result** of call will also have concrete refinement.</div>

<div class="fragment">

\begin{code}
{-@ o' :: Odd  @-}
o' = maxInt 3 7     -- p := \v -> Odd v 

{-@ e' :: Even @-}
e' = maxInt 2 8     -- p := \v -> Even v 
\end{code}

</div>

Using Abstract Refinements
--------------------------

Or any other property ...

<br>

<div class="fragment">

\begin{code}
{-@ type RGB = {v:_ | (0 <= v && v < 256)} @-}

{-@ rgb :: RGB @-}
rgb = maxInt 56 8
\end{code}

</div>


Recap
-----

1. Refinements: Types + Predicates
2. Subtyping: SMT Implication
3. Measures: Strengthened Constructors
4. <div class="fragment">**Abstract Refinements** over Types

<br>
<br>

<div class="fragment">
  Abstract Refinements are *very* expressive ... <a href="06_Inductive.lhs.slides.html" target="_blank">[continue]</a>
</div>

