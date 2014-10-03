
 {#measures}
============

Measuring Data Types
--------------------

<div class="hidden">

\begin{code}

{-# LIQUID "--no-termination" #-}
{-# LIQUID "--full" #-}

module Measures where
import Prelude hiding ((!!), length)
import Language.Haskell.Liquid.Prelude


length      :: L a -> Int
(!)         :: L a -> Int -> a
insert      :: Ord a => a -> L a -> L a
insertSort  :: Ord a => [a] -> L a

infixr `C`
\end{code}

</div>


Measuring Data Types 
====================

Recap
-----

1. <div class="fragment">**Refinements:** Types + Predicates</div>
2. <div class="fragment">**Subtyping:** SMT Implication</div>


Example: Length of a List 
-------------------------

Given a type for lists:

<br>

\begin{code}
data L a = N | C a (L a)
\end{code}

<div class="fragment">
<br>

We can define the **length** as:

<br>

\begin{code}
{-@ measure llen  :: (L a) -> Int
    llen (N)      = 0
    llen (C x xs) = 1 + (llen xs)  @-}
\end{code}

<div class="hidden">

\begin{code}
{-@ data L [llen] a = N | C {hd :: a, tl :: L a } @-}
{-@ invariant {v: L a | 0 <= llen v}              @-} 
\end{code}

</div>

Example: Length of a List 
-------------------------

\begin{spec}
{-@ measure llen  :: (L a) -> Int
    llen (N)      = 0
    llen (C x xs) = 1 + llen xs  @-}
\end{spec}

<br>

We **strengthen** data constructor types

<br>

\begin{spec} <div/>
data L a where 
  N :: {v: L a | (llen v) = 0}
  C :: a -> t:_ -> {v:_| llen v = 1 + llen t}
\end{spec}

Measures Are Uninterpreted
--------------------------

\begin{spec} <br>
data L a where 
  N :: {v: L a | (llen v) = 0}
  C :: a -> t:_ -> {v:_| llen v = 1 + llen t}
\end{spec}

<br>

`llen` is an **uninterpreted function** in SMT logic

Measures Are Uninterpreted
--------------------------

<br>

In SMT, [uninterpreted function](http://fm.csl.sri.com/SSFT12/smt-euf-arithmetic.pdf) $f$ obeys **congruence** axiom:

<br>

$$\forall \overline{x}, \overline{y}. \overline{x} = \overline{y} \Rightarrow
f(\overline{x}) = f(\overline{y})$$

<br>

<div class="fragment">
Other properties of `llen` asserted when typing **fold** & **unfold**
</div>

<br>

<div class="fragment">
Crucial for *efficient*, *decidable* and *predictable* verification.
</div>

Measures Are Uninterpreted
--------------------------

Other properties of `llen` asserted when typing **fold** & **unfold**

<br>

<div class="fragment">
\begin{spec}**Fold**<br>
z = C x y     -- z :: {v | llen v = 1 + llen y}
\end{spec}
</div>

<br>

<div class="fragment">
\begin{spec}**Unfold**<br>
case z of 
  N     -> e1 -- z :: {v | llen v = 0}
  C x y -> e2 -- z :: {v | llen v = 1 + llen y}
\end{spec}
</div>


Measured Refinements
--------------------

Now, we can verify:

<br>

\begin{code}
{-@ length      :: xs:L a -> EqLen xs @-}
length N        = 0
length (C _ xs) = 1 + length xs
\end{code}

<div class="fragment">

<br>

Where `EqLen` is a type alias:

\begin{code}
{-@ type EqLen Xs = {v:Nat | v = llen Xs} @-}
\end{code}

</div>

List Indexing Redux
-------------------

We can type list lookup:

\begin{code}
{-@ (!)      :: xs:L a -> LtLen xs -> a @-}
(C x _)  ! 0 = x
(C _ xs) ! i = xs ! (i - 1)
_        ! _ = liquidError "never happens!"
\end{code}

<br>

<div class="fragment">
Where `LtLen` is a type alias:

\begin{code}
{-@ type LtLen Xs = {v:Nat | v < llen Xs} @-}
\end{code}

<br>

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellMeasure.hs" target= "_blank">Demo:</a> 
&nbsp; What if we *remove* the precondition?

</div>

Multiple Measures
-----------------

<br>

Support **many** measures on a type ...

<br>

<div class="fragment">
... by **conjoining** the constructor refinements.
</div>

<br>
<br>

[[Skip...]](#/refined-data-cons)


<!--

Multiple Measures
=================

 {#adasd}
---------

We allow *many* measures for a type

Ex: List Emptiness 
------------------

Measure describing whether a `List` is empty 

\begin{code}
{-@ measure isNull :: (L a) -> Prop
    isNull (N)      = true
    isNull (C x xs) = false           @-}
\end{code}

<br>

<div class="fragment">
We **strengthen** data constructors

\begin{spec} <div/> 
data L a where 
  N :: {v : L a | (isNull v)}
  C :: a -> L a -> {v:(L a) | not (isNull v)}
\end{spec}

</div>

Conjoining Refinements
----------------------

Data constructor refinements are **conjoined** 

\begin{spec} <br>
data L a where 
  N :: {v:L a |  (llen v) = 0 
              && (isNull v) }
  C :: a 
    -> xs:L a 
    -> {v:L a |  (llen v) = 1 + (llen xs) 
              && not (isNull v)          }
\end{spec}

-->

Multiple Measures: Red-Black Trees
==================================

 {#rbtree}
----------

<img src="../img/RedBlack.png" height=300px>

+ <div class="fragment">**Color:** `Red` nodes have `Black` children</div>
+ <div class="fragment">**Height:** Number of `Black` nodes equal on *all paths*</div>
<br>

[[Skip...]](#/refined-data-cons)

Basic Type 
----------

\begin{spec} <br>
data Tree a = Leaf 
            | Node Color a (Tree a) (Tree a)

data Color  = Red 
            | Black
\end{spec}

Color Invariant 
---------------

`Red` nodes have `Black` children

<div class="fragment">
\begin{spec} <br>
measure isRB        :: Tree a -> Prop
isRB (Leaf)         = true
isRB (Node c x l r) = c=Red => (isB l && isB r)
                      && isRB l && isRB r
\end{spec}
</div>

<div class="fragment">
\begin{spec} where <br>
measure isB         :: Tree a -> Prop 
isB (Leaf)          = true
isB (Node c x l r)  = c == Black 
\end{spec}
</div>

*Almost* Color Invariant 
------------------------

<br>

Color Invariant **except** at root. 

<br>

<div class="fragment">
\begin{spec} <br>
measure isAlmost        :: Tree a -> Prop
isAlmost (Leaf)         = true
isAlmost (Node c x l r) = isRB l && isRB r
\end{spec}
</div>


Height Invariant
----------------

Number of `Black` nodes equal on **all paths**

<div class="fragment">
\begin{spec} <br>
measure isBH        :: RBTree a -> Prop
isBH (Leaf)         =  true
isBH (Node c x l r) =  bh l = bh r 
                    && isBH l && isBH r 
\end{spec}
</div>

<div class="fragment">
\begin{spec} where <br>
measure bh        :: RBTree a -> Int
bh (Leaf)         = 0
bh (Node c x l r) = bh l 
                  + if c = Red then 0 else 1
\end{spec}
</div>

Refined Type 
------------

\begin{spec} <br>
-- Red-Black Trees
type RBT a  = {v:Tree a | isRB v && isBH v}

-- Almost Red-Black Trees
type ARBT a = {v:Tree a | isAlmost v && isBH v}
\end{spec}

<br>

[Details](https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/pos/RBTree.hs)

<!--

Measures vs. Index Types
========================

Decouple Property & Type 
------------------------

Unlike [indexed types](http://dl.acm.org/citation.cfm?id=270793) ...

<br>

<div class="fragment">

+ Measures **decouple** properties from structures

+ Support **multiple** properties over structures 

+ Enable  **reuse** of structures in different contexts                 

</div>

<br>

<div class="fragment">Invaluable in practice!</div>

-->

Refined Data Constructors
=========================

 {#refined-data-cons}
---------------------

Can encode invariants **inside constructors**

<div class="fragment">

<br>

\begin{code}
{-@ data L a = N
             | C { x  :: a 
                 , xs :: L {v:a| x <= v} } @-}
\end{code}
</div>
<br>

<div class="fragment">
Head `x` is less than **every** element of tail `xs`
</div>

<br>

<div class="fragment">
i.e. specifies **increasing** Lists 
</div>

Increasing Lists 
----------------

\begin{spec} <br>
data L a where
  N :: L a
  C :: x:a -> xs: L {v:a | x <= v} -> L a
\end{spec}

<br>

- <div class="fragment">We **check** property when **folding** `C`</div>
- <div class="fragment">We **assume** property when **unfolding** `C`</div>

Increasing Lists 
----------------

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellInsertSort.hs" target= "_blank">Demo: Insertion Sort</a> (hover for inferred types) 

<br>

\begin{code}
insertSort xs = foldr insert N xs

insert y (x `C` xs) 
  | y <= x    = y `C` (x `C` xs)
  | otherwise = x `C` insert y xs
insert y N    = y `C` N    
\end{code}

<br>

Recap
-----

<br>
<br>



1. Refinements: Types + Predicates
2. Subtyping: SMT Implication
3. **Measures:** Strengthened Constructors

<br>

<div class="fragment">Logic + Analysis for Collections</div>

<br>
<br>

<div class="fragment"><a href="03_HigherOrderFunctions.lhs.slides.html" target="_blank">[continue]</a></div>
