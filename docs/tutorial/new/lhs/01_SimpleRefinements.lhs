 {#simplerefinements}
=======================

Simple Refinement Types
-----------------------

<div class="hidden">

\begin{code}
module SimpleRefinements where
import Language.Haskell.Liquid.Prelude

-- boring haskell type sigs
zero     :: Int
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
{-@ zero :: {v : Int | v = 0} @-}
zero     =  0
\end{code}

<br>

<div class="fragment">
Refinement types via special comments
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

--------    ----------------------------
  **If**    `p => q`

**Then**    `{v : t | p} <: {v : t | q}`
--------    ----------------------------


Subtyping is Implication
------------------------

<br>

--------  ---------------------------------
  **As**  `v=0` *implies* `0<=v`

  **So**  `{v:Int | v=0} <: {v:Int | 0<=v}`
--------  ---------------------------------


Example: Natural Numbers
------------------------

<br>

\begin{code} &nbsp;
type Nat = {v : Int | 0 <= v}
\end{code}

<br>

And, via SMT based subtyping LiquidHaskell verifies:

<br>

\begin{code}
{-@ zero' :: Nat @-}
zero'     :: Int
zero'     =  0
\end{code}


Lists: Universal Invariants 
---------------------------

Constructors enable *universally quantified* invariants.

For example, we define a list:

\begin{code}
infixr `C`
data L a = N | C a (L a)
\end{code}

<br>

And specify that, *every element* in a list is non-negative:

\begin{code}
{-@ natList :: L Nat @-}
natList     :: L Int
natList     =  0 `C` 1 `C` 3 `C` N
\end{code}

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo:</a> 
Lets see what happens if `natList` contained a negative number. 

Refinement Function Types
-------------------------

Consider a `safeDiv` operator: <br>

\begin{code}
safeDiv    :: Int -> Int -> Int
safeDiv x y = x `div` y
\end{code}

<br>
We can use refinements to specify a **precondition**: divisor is **non-zero** <br>

\begin{code}
{-@ safeDiv :: Int -> {v:Int | v != 0} -> Int @-}
\end{code}

<br>

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo:</a> 
Lets see what happens if the preconditions cannot be
proven. 

Dependent Function Types
------------------------

\begin{code} Consider a list indexing function:
(!!)         :: L a -> Int -> a
(C x _) !! 0 = x
(C _ xs)!! n = xs!!(n-1)
_       !! _ = liquidError "This should not happen!"
\end{code}

<br>

We desire a **precondition** that index `i` be between `0` and **list length**.

We use **measures** to talk about the length of a list in **logic**.


