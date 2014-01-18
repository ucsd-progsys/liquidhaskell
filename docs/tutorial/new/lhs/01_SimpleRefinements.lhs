 {#simplerefinements}
=======================

Simple Refinement Types
-----------------------

<div class="hidden">

\begin{code}
module SimpleRefinements where
import Language.Haskell.Liquid.Prelude
import Prelude hiding (abs, max)

-- boring haskell type sigs
zero    :: Int
zero'   :: Int
safeDiv :: Int -> Int -> Int
abs     :: Int -> Int
nats    :: L Int
\end{code}

</div>


Simple Refinement Types
=======================


Types + Predicates 
------------------


Example
-------

Integers equal to `0`

<br>

\begin{code}
{-@ type EqZero = {v:Int | v = 0} @-}
\end{code}


Example
-------

Integers equal to `0`

<br>

\begin{code}
{-@ zero :: EqZero @-}
zero     =  0
\end{code}

<br>

<div class="fragment">
Refinement types via special comments `{-@ ... @-}`
</div>


<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo</a> 
Lets take a look.
</div>

 {#refinementsArePredicates}
============================

Refinements Are Predicates
--------------------------


Refinements Are Predicates
==========================

Subtyping is Implication
------------------------

[Predicate Subtyping](http://pvs.csl.sri.com/papers/subtypes98/tse98.pdf)


Subtyping is Implication
------------------------

<br>

--------  ---  ---------------------------------------------
  **If**   :   Refinement of `S` *implies* refinement of `T` 

**Then**   :   `S` is a *subtype* of `T`
--------  ---  ---------------------------------------------

<br>


Subtyping is Implication
------------------------


<br>

--------   ---     ----------------------------
  **If**    :      `p => q`
                
**Then**    :      `{v : t | p} <: {v : t | q}`
--------   ---     ----------------------------


Subtyping is Implication
------------------------

<br>

--------    ---  ---------------------------------------------------
  **As**     :   `v=0` *implies* `0<=v` ... via SMT
                 
  **So**     :   `{v:Int | v=0} <: {v:Int | 0<=v}`
--------    ---  ---------------------------------------------------


Example: Natural Numbers
------------------------

\begin{code} . 
type Nat = {v : Int | 0 <= v}
\end{code}

<br>

Via SMT, LiquidHaskell infers `EqZero <: Nat`, hence:

<br>

\begin{code}
{-@ zero' :: Nat @-}
zero'     =  zero
\end{code}

 {#universalinvariants}
=======================

Types Yield Universal Invariants
--------------------------------

(Notoriously tedious with pure SMT)

Types Yield Universal Invariants
================================

Example: Lists
--------------

<div class="hidden">

\begin{code}
infixr `C`
\end{code}

</div>

\begin{code}
data L a = N | C a (L a)
\end{code}

<br>

*Every element* in `nats` is non-negative:

\begin{code}
{-@ nats :: L Nat @-}
nats     =  0 `C` 1 `C` 3 `C` N
\end{code}

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo:</a> 
What if `nats` contained `-2`? 

 {#functiontypes}
=================

Contracts = Function Types
--------------------------

Function Types
==============

Example: `safeDiv`
------------------

<br>

\begin{code}
{-@ safeDiv :: Int -> {v:Int | v /= 0} -> Int @-}
safeDiv x y = x `div` y
\end{code}

<br>

<div class="fragment">

+ *Input* type specifies *pre-condition*
+ Divisor is *non-zero* 


<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo:</a> 
What if precondition does not hold?

<div>

Example: `max`
--------------

<br>

\begin{code}
{-@ abs       :: x:Int -> Nat @-}
abs x 
  | 0 <= x    = x 
  | otherwise = 0 - x
\end{code}

<br>

<div class="fragment">

+ *Output* type specifies *post-condition*
+ Result is non-negative

<div>

{#dependentfunctions}
=====================

Dependent Function Types
------------------------

+ Outputs **refer to** inputs
+ *Relational* invariants


Dependent Function Types
========================

HEREHEREHEREHERERHERERHEREHERHERHERE

Example: `range`
----------------

\begin{code}
type IntBtwn I J  = {v:Int | (I <= v && v < j)}


range             :: i:Int -> j:Int -> L (Btwn i j)
range i j         = go
  where
    go n
      | n < j     = n `C` go (n + 1)  
      | otherwise = N
\end{code}



Example: Indexing Into List
---------------------------

\begin{code} Consider a list indexing function:
(!!)         :: L a -> Int -> a
(C x _) !! 0 = x
(C _ xs)!! n = xs!!(n-1)
_       !! _ = liquidError "This should not happen!"
\end{code}

<br>

We desire a **precondition** that index `i` be between `0` and **list length**.

We use **measures** to talk about the length of a list in **logic**.


