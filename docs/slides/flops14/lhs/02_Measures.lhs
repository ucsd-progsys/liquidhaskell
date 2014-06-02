
 {#measures}
============

Measuring Data Types
--------------------

<div class="hidden">

\begin{code}
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

</div>

Example: Length of a List 
-------------------------

\begin{code} <div/>
{-@ measure llen  :: (L a) -> Int
    llen (N)      = 0
    llen (C x xs) = 1 + (llen xs)  @-}
\end{code}

<br>

LiquidHaskell **strengthens** data constructor types

<br>

\begin{code} <div/>
data L a where 
  N :: {v: L a | (llen v) = 0}
  C :: a -> t:_ -> {v:_| llen v = 1 + llen t}
\end{code}

Measures Are Uninterpreted
--------------------------

\begin{code} <br>
data L a where 
  N :: {v: L a | (llen v) = 0}
  C :: a -> t:_ -> {v:_| llen v = 1 + llen t}
\end{code}

<br>

`llen` is an **uninterpreted function** in SMT logic

Measures Are Uninterpreted
--------------------------

<br>

In SMT, [uninterpreted function](http://fm.csl.sri.com/SSFT12/smt-euf-arithmetic.pdf) `f` obeys *congruence* axiom:

<br>

`forall x y. (x = y) => (f x) = (f y)`

<br>

<div class="fragment">
All other facts about `llen` asserted at **fold** and **unfold**
</div>

Measures Are Uninterpreted
--------------------------

Facts about `llen` asserted at *syntax-directed* **fold** and **unfold**

<br>

<div class="fragment">
\begin{code}**Fold**<br>
z = C x y     -- z :: {v | llen v = 1 + llen y}
\end{code}
</div>

<br>

<div class="fragment">
\begin{code}**Unfold**<br>
case z of 
  N     -> e1 -- z :: {v | llen v = 0}
  C x y -> e2 -- z :: {v | llen v = 1 + llen y}
\end{code}
</div>


Measured Refinements
--------------------

Now, we can verify:

<br>

\begin{code}
{-@ length      :: xs:L a -> (EqLen xs) @-}
length N        = 0
length (C _ xs) = 1 + length xs
\end{code}

<div class="fragment">

<br>

Where `EqLen` is a type alias:

\begin{code}
{-@ type EqLen Xs = {v:Nat | v = (llen Xs)} @-}
\end{code}

</div>

List Indexing Redux
-------------------

We can type list indexed lookup:

<br>

\begin{code}
{-@ (!)      :: xs:L a -> (LtLen xs) -> a @-}
(C x _)  ! 0 = x
(C _ xs) ! i = xs ! (i - 1)
_        ! _ = liquidError "never happens!"
\end{code}

<br>

<div class="fragment">
Where `LtLen` is a type alias:

<br>

\begin{code}
{-@ type LtLen Xs = {v:Nat | v < (llen Xs)} @-}
\end{code}

</div>

List Indexing Redux
-------------------

Now we can type list indexed lookup:

\begin{code} <br>
{-@ (!)      :: xs:L a -> (LtLen xs) -> a @-}
(C x _)  ! 0 = x
(C _ xs) ! i = xs ! (i - 1)
_        ! _ = liquidError "never happens!"
\end{code}

<br>

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellMeasure.hs" target= "_blank">Demo:</a> 
What if we *remove* the precondition?

Multiple Measures
=================

 {#adasd}
---------

LiquidHaskell allows *many* measures for a type


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
LiquidHaskell **strengthens** data constructors

\begin{code} <div/> 
data L a where 
  N :: {v : L a | (isNull v)}
  C :: a -> L a -> {v:(L a) | not (isNull v)}
\end{code}

</div>

Conjoining Refinements
----------------------

Data constructor refinements are **conjoined** 

\begin{code} <br>
data L a where 
  N :: {v:L a |  (llen v) = 0 
              && (isNull v) }
  C :: a 
    -> xs:L a 
    -> {v:L a |  (llen v) = 1 + (llen xs) 
              && not (isNull v)          }
\end{code}

Multiple Measures: Red-Black Trees
==================================

 {#asdad}
---------

<img src="../img/RedBlack.png" height=300px>

+ <div class="fragment">**Color Invariant:** `Red` nodes have `Black` children</div>
+ <div class="fragment">**Height Invariant:** Number of `Black` nodes equal on *all paths*</div>
<br>

[[Skip...]](#/4)

Basic Type 
----------

\begin{code} <br>
data Tree a = Leaf 
            | Node Color a (Tree a) (Tree a)

data Color  = Red 
            | Black
\end{code}

Color Invariant 
---------------

`Red` nodes have `Black` children

<div class="fragment">
\begin{code} <br>
measure isRB        :: Tree a -> Prop
isRB (Leaf)         =  true
isRB (Node c x l r) =  c=R => (isB l && isB r)
                    && isRB l && isRB r
\end{code}
</div>

<div class="fragment">
\begin{code} where <br>
measure isB         :: Tree a -> Prop 
isB (Leaf)          = true
isB (Node c x l r)  = c == Black 
\end{code}
</div>

*Almost* Color Invariant 
------------------------

<br>
<br>

Color Invariant **except** at root. 

<br>
<br>

<div class="fragment">
\begin{code} <br>
measure isAlmost        :: Tree a -> Prop
isAlmost (Leaf)         = true
isAlmost (Node c x l r) = isRB l && isRB r
\end{code}
</div>


Height Invariant
----------------

Number of `Black` nodes equal on **all paths**

<div class="fragment">
\begin{code} <br>
measure isBH        :: RBTree a -> Prop
isBH (Leaf)         =  true
isBH (Node c x l r) =  bh l = bh r 
                    && isBH l && isBH r 
\end{code}
</div>

<div class="fragment">
\begin{code} where <br>
measure bh        :: RBTree a -> Int
bh (Leaf)         = 0
bh (Node c x l r) = bh l 
                  + if c == Red then 0 else 1
\end{code}
</div>

Refined Type 
------------

\begin{code} <br>
-- Red-Black Trees
type RBT a  = {v:Tree a | isRB v && isBH v}

-- Almost Red-Black Trees
type ARBT a = {v:Tree a | isAlmost v && isBH v}
\end{code}

<br>

[Details](https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/pos/RBTree.hs)


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

Refined Data Constructors
=========================

 {#asd}
-------

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

\begin{code} <br>
data L a where
  N :: L a
  C :: x:a -> xs: L {v:a | x <= v} -> L a
\end{code}

<br>

- <div class="fragment">LiquidHaskell **checks** property when **folding** `C`</div>
- <div class="fragment">LiquidHaskell **assumes** property when **unfolding** `C`</div>

Increasing Lists 
----------------

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellInsertSort.hs" target= "_blank">Demo: Insertion Sort</a> (hover for inferred types) 

<br>

\begin{code}
insertSort = foldr insert N

insert y (x `C` xs) 
  | y <= x    = y `C` (x `C` xs)
  | otherwise = x `C` insert y xs
insert y N    = y `C` N    
\end{code}

<br>

<div class="fragment">**Problem 1:** What if we need *both* [increasing and decreasing lists](http://web.cecs.pdx.edu/~sheard/Code/QSort.html)?</div>

Recap
-----

1. Refinements: Types + Predicates
2. Subtyping: SMT Implication
3. <div class="fragment">**Measures:** Strengthened Constructors</div>
    - <div class="fragment">**Decouple** property from structure</div>
    - <div class="fragment">**Reuse** structure across *different* properties</div>

<br>

<div class="fragment"><a href="03_HigherOrderFunctions.lhs.slides.html" target="_blank">[continue]</a></div>
