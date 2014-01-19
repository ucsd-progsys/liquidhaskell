 {#simplerefinements}
=======================

Simple Refinement Types
-----------------------

<div class="hidden">

\begin{code}
{-@ LIQUID "--no-termination" @-}
module SimpleRefinements where
import Language.Haskell.Liquid.Prelude
import Prelude hiding (abs, max)

-- boring haskell type sigs
zero    :: Int
zero'   :: Int
safeDiv :: Int -> Int -> Int
abs     :: Int -> Int
nats    :: L Int
evens   :: L Int
odds    :: L Int
range   :: Int -> Int -> L Int
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

Types = Universal Invariants
----------------------------

(Notoriously hard with *pure* SMT)

Types Yield Universal Invariants
================================

Example: Lists
--------------

<div class="hidden">

\begin{code}
infixr `C`
\end{code}

</div>

<br>

\begin{code}
data L a = N | C a (L a)
\end{code}

<br>

<div class="fragment">

*Every element* in `nats` is non-negative:

<br>

\begin{code}
{-@ nats :: L Nat @-}
nats     =  0 `C` 1 `C` 3 `C` N
\end{code}

</div>

<br>

<div class="fragment">

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo:</a> 
What if `nats` contained `-2`? 

</div>

Example: Even/Odd Lists
-----------------------

<br>

\begin{code}
type Even = {v:Int | v mod 2 =  0}
type Odd  = {v:Int | v mod 2 /= 0}
\end{code}

<br>

<div class="fragment">

\begin{code}
{-@ evens :: L Even @-}
evens     =  0 `C` 2 `C` 4 `C` N

{-@ odds  :: L Odd  @-}
odds      =  1 `C` 3 `C` 5 `C` N 
\end{code}

</div>

<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo:</a> 
What if `evens` contained `1`? 
</div>

 {#functiontypes}
=================

Contracts = Function Types
--------------------------

Contracts: Function Types
=========================


Example: `safeDiv`
------------------

<br>

**Precondition** divisor is *non-zero*.

<br>

<div class="fragment">
\begin{code}
{-@ type NonZero = {v:Int | v /= 0} @-}
\end{code}
</div>

<br>

Example: `safeDiv`
------------------

<br>

+ **Pre-condition** divisor is *non-zero*.
+ **Input type** specifies *pre-condition*

<br>

\begin{code}
{-@ safeDiv :: Int -> NonZero -> Int @-}
safeDiv x y = x `div` y
\end{code}

<br>

<div class="fragment">

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo:</a> 
What if precondition does not hold?

</div>

Example: `abs`
--------------

<br>

+ **Postcondition** result is non-negative
+ **Output type** specifies *post-condition*

<br>

\begin{code}
{-@ abs       :: x:Int -> Nat @-}
abs x 
  | 0 <= x    = x 
  | otherwise = 0 - x
\end{code}



 {#dependentfunctions}
======================

Dependent Function Types
------------------------

+ Outputs *refer to* inputs
+ *Relational* invariants


Dependent Function Types
========================

Example: `range`
----------------

`(range i j)` returns `Int`s between `i` and `j`


Example: `range`
----------------

`(range i j)` returns `Int`s between `i` and `j`

<br>

\begin{code}
{-@ type Btwn I J = {v:_|(I <= v && v < J)} @-}
\end{code}

Example: `range`
----------------

`(range i j)` returns `Int`s between `i` and `j`

<br>

\begin{code}
{-@ range :: i:Int -> j:Int -> L (Btwn i j) @-}
range i j         = go i
  where
    go n
      | n < j     = n `C` go (n + 1)  
      | otherwise = N
\end{code}

<br>

<div class="fragment">
**Question:** What is the type of `go` ?
</div>


Example: Indexing Into List
---------------------------

\begin{code} 
(!)          :: L a -> Int -> a
(C x _)  ! 0 = x
(C _ xs) ! i = xs ! (i - 1)
_        ! _ = liquidError "Oops!"
\end{code}

<br>

<div class="fragment">(Mouseover to view type of `liquidError`)</div>

<br>

- <div class="fragment">**Q:** How to ensure safety? </div>
- <div class="fragment">**A:** Precondition: `i` between `0` and list **length**.

<div class="fragment">Need way to [measure](#measures) *length of a list* ...</div>


