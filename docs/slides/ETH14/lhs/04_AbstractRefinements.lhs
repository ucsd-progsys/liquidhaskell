  {#abstractrefinements}
========================

<div class="hidden">

\begin{code}
module AbstractRefinements where

import Prelude 
import Language.Haskell.Liquid.Prelude
{-@ LIQUID "--no-termination" @-}

-- o,no        :: Int
maxInt       :: Int -> Int -> Int
\end{code}
</div>



Abstract Refinements
--------------------


Abstract Refinements
====================

A Tricky Problem
----------------

<br>

<div class="fragment">

**Problem** 

Require *context-dependent* invariants & summaries for HOFs.

</div>

<br>
<br>

<div class="fragment">

**Example** 

How to summarize *iteration-dependence* for higher-order `loop`?

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

\begin{spec} <br> 
maxInt     :: Int -> Int -> Int 
maxInt x y = if y <= x then x else y
\end{spec}



Example: `maxInt` 
-----------------

Has **many incomparable** refinement types/summaries

\begin{spec}<br>
maxInt :: Nat  -> Nat  -> Nat
maxInt :: Even -> Even -> Even
maxInt :: Odd  -> Odd  -> Odd 
\end{spec}

<br>

<div class="fragment">*Which* should we use?</div>


Refinement Polymorphism 
-----------------------

`maxInt` returns **one of** its two inputs `x` and `y` 

<div class="fragment">

<div align="center">

<br>

---------   ---   -------------------------------------------
   **If**    :    the *inputs* satisfy a property  

 **Then**    :    the *output* satisfies that property
---------   ---   -------------------------------------------

<br>

</div>
</div>

<div class="fragment">Above holds **for all properties**!</div>

<br>

<div class="fragment"> 

**Need to abstract properties over types**

</div>

Parametric Refinements 
----------------------

Enable *quantification over refinements* ...

<br>

<div class="fragment">
\begin{code}
{-@ maxInt :: forall <p :: Int -> Prop>. 
                Int<p> -> Int<p> -> Int<p>  @-}

maxInt x y = if x <= y then y else x 
\end{code}
</div>

<br>

<div class="fragment">Type says: **for any** `p` that is a property of `Int`, </div>

- <div class="fragment">`max` **takes** two `Int`s that satisfy `p`,</div>

- <div class="fragment">`max` **returns** an `Int` that satisfies `p`.</div>

Parametric Refinements 
----------------------

Enable *quantification over refinements* ...

<br>

\begin{spec}<div/>
{-@ maxInt :: forall <p :: Int -> Prop>. 
                Int<p> -> Int<p> -> Int<p>  @-}

maxInt x y = if x <= y then y else x 
\end{spec}

<br>

[Key idea: ](http://goto.ucsd.edu/~rjhala/papers/abstract_refinement_types.html)
&nbsp; `Int<p>` &nbsp; is just  &nbsp; $\reft{v}{\Int}{p(v)}$ 

<br>

Abstract Refinement is **uninterpreted function** in SMT logic

Parametric Refinements 
----------------------

\begin{spec}<br>
{-@ maxInt :: forall <p :: Int -> Prop>. 
                Int<p> -> Int<p> -> Int<p>  @-}

maxInt x y = if x <= y then y else x 
\end{spec}

<br>

**Check Implementation via SMT**

Parametric Refinements 
----------------------

\begin{spec}<br>
{-@ maxInt :: forall <p :: Int -> Prop>. 
                Int<p> -> Int<p> -> Int<p>  @-}

maxInt x y = if x <= y then y else x 
\end{spec}

<br>

**Check Implementation via SMT**

<br>

$$\begin{array}{rll}
\ereft{x}{\Int}{p(x)},\ereft{y}{\Int}{p(y)} & \vdash \reftx{v}{v = y} & \subty \reftx{v}{p(v)} \\
\ereft{x}{\Int}{p(x)},\ereft{y}{\Int}{p(y)} & \vdash \reftx{v}{v = x} & \subty \reftx{v}{p(v)} \\
\end{array}$$

Parametric Refinements 
----------------------

\begin{spec}<br>
{-@ maxInt :: forall <p :: Int -> Prop>. 
                Int<p> -> Int<p> -> Int<p>  @-}

maxInt x y = if x <= y then y else x 
\end{spec}

<br>

**Check Implementation via SMT**

<br>

$$\begin{array}{rll}
{p(x)} \wedge {p(y)} & \Rightarrow {v = y} & \Rightarrow {p(v)} \\
{p(x)} \wedge {p(y)} & \Rightarrow {v = x} & \Rightarrow {p(v)} \\
\end{array}$$


Using Abstract Refinements
--------------------------

- <div class="fragment">**If** we call `maxInt` with args satisfying *common property*,</div>
- <div class="fragment">**Then** `p` instantiated property, *result* gets same property.</div>

<br>

<div class="fragment">

\begin{code}
{-@ xo :: Odd  @-}
xo = maxInt 3 7     -- p := \v -> Odd v 

{-@ xe :: Even @-}
xe = maxInt 2 8     -- p := \v -> Even v 
\end{code}

</div>

<br>

<div class="fragment">
**Infer Instantiation by Liquid Typing**

At call-site, instantiate `p` with unknown $\kvar{p}$ and solve!
</div>

Recap
-----

1. Refinements: Types + Predicates
2. Subtyping: SMT Implication
3. Measures: Strengthened Constructors
4. **Abstract Refinements** over Types

<br>
<br>

<div class="fragment">
  Abstract Refinements decouple invariants from **code** ...

<br>

<a href="06_Inductive.lhs.slides.html" target="_blank">[continue]</a>
</div>

