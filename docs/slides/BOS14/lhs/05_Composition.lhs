Abstract Refinements {#composition}
===================================

Very General Mechanism 
----------------------

**Next:** Lets add parameters...

<div class="hidden">
\begin{code}
module Composition where

import Prelude hiding ((.))

plus     :: Int -> Int -> Int
plus3'   :: Int -> Int
\end{code}
</div>


Example: `plus`
---------------

\begin{code}
{-@ plus :: x:_ -> y:_ -> {v:_ | v=x+y} @-}
plus x y = x + y
\end{code}


Example: `plus 3` 
-----------------

<br>

\begin{code}
{-@ plus3' :: x:Int -> {v:Int | v = x + 3} @-}
plus3'     = plus 3
\end{code}

<br>

Easily verified by LiquidHaskell

A Composed Variant
------------------

Lets define `plus3` by *composition*

A Composition Operator 
----------------------

\begin{code}
(#) :: (b -> c) -> (a -> b) -> a -> c
(#) f g x = f (g x)
\end{code}


`plus3` By Composition
-----------------------

\begin{code}
{-@ plus3'' :: x:Int -> {v:Int | v = x + 3} @-}
plus3''     = plus 1 # plus 2
\end{code}

<br>

Yikes! Verification *fails*. But why?

<br>

<div class="fragment">(Hover mouse over `#` for a clue)</div>

How to type compose (#) ? 
-------------------------

This specification is *too weak* <br>

\begin{spec} <br>
(#) :: (b -> c) -> (a -> b) -> (a -> c)
\end{spec}

<br>

Output type does not *relate* `c` with `a`!

How to type compose (.) ?
-------------------------

Write specification with abstract refinement type:

<br>

\begin{code}
{-@ (.) :: forall <p :: b->c->Prop, 
                   q :: a->b->Prop>.
             f:(x:b -> c<p x>) 
          -> g:(x:a -> b<q x>) 
          -> y:a -> exists[z:b<q y>].c<p z>
 @-}
(.) f g y = f (g y)
\end{code}

Using (.) Operator 
------------------

<br>

\begin{code}
{-@ plus3 :: x:Int -> {v:Int | v = x + 3} @-}
plus3     = plus 1 . plus 2
\end{code}

<br>

<div class="fragment">*Verifies!*</div>


Using (.) Operator 
------------------

\begin{spec} <br>
{-@ plus3 :: x:Int -> {v:Int | v = x + 3} @-}
plus3     = plus 1 . plus 2
\end{spec}

<br>

LiquidHaskell *instantiates*

- `p` with `\x -> v = x + 1`
- `q` with `\x -> v = x + 2`

Using (.) Operator 
------------------

\begin{spec} <br>
{-@ plus3 :: x:Int -> {v:Int | v = x + 3} @-}
plus3     = plus 1 . plus 2
\end{spec}

<br> To *infer* that output of `plus3` has type: 

`exists [z:{v = y + 2}].{v = z + 1}`

<div class="fragment">

`<:`

`{v:Int|v=3}`
</div>


Recap
-----

1. **Refinements:** Types + Predicates
2. **Subtyping:** SMT Implication
3. **Measures:** Strengthened Constructors
4. **Abstract:** Refinements over Type Signatures
    + <div class="fragment">*Dependencies* using refinement parameters</div>
