
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
\end{code}

</div>

Measuring Data Types 
====================

Recap
-----

1. <div class="fragment">**Refinements:** Types + Predicates</div>
2. <div class="fragment">**Subtyping:** SMT Implication</div>


---   -----------------------   ---  -------------------------
 1.      **Refinement Types**    :   Types + Predicates
 2.             **Subtyping**    :   SMT / Logical Implication 
---   -----------------------   ---  -------------------------


Example: Lists 
--------------

<div class="hidden">

\begin{code}
infixr `C`
\end{code}

</div>

<br>

\begin{code}
data L a = N 
         | C a (L a)
\end{code}

Example: Length of a List 
-------------------------

\begin{code}
{-@ measure llen  :: (L a) -> Int
    llen (N)      = 0
    llen (C x xs) = 1 + (llen xs)  @-}
\end{code}

<br>

<div class="fragment">
LiquidHaskell *strengthens* data constructor types
\begin{code} <div/>
data L a where 
  N :: {v: L a | (llen v) = 0}
  C :: a -> xs:L a 
         -> {v:L a | (llen v) = 1 + (llen xs)}
\end{code}
</div>

Measures Are Uninterpreted
--------------------------

\begin{code} <br>
data L a where 
  N :: {v: L a | (llen v) = 0}
  C :: a -> xs:L a 
         -> {v:L a | (llen v) = 1 + (llen xs)}
\end{code}

<br>

`llen` is an *uninterpreted function* in SMT logic

Measures Are Uninterpreted
--------------------------

In SMT, [uninterpreted function](http://fm.csl.sri.com/SSFT12/smt-euf-arithmetic.pdf) `f` obeys *congruence* axiom:

`forall x y. (x = y) => (f x) = (f y)`

<br>

<div class="fragment">
All other facts about `llen` asserted at *fold* and *unfold*
</div>

Measures Are Uninterpreted
--------------------------

All other facts about `llen` asserted at *fold* and *unfold*

<br>

<div class="fragment">
\begin{code}**Fold**<br>
z = C x y -- z :: {v | llen v = 1 + llen y}
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
length (C _ xs) = 1 + (length xs)
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

Where `LtLen` is a type alias:

\begin{code}
{-@ type LtLen Xs = {v:Nat | v < (llen Xs)} @-}
\end{code}


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
-----------------

LiquidHaskell allows *many* measures for a type


Multiple Measures 
-----------------

**Example:** Nullity of a `List` 

\begin{code}
{-@ measure isNull :: (L a) -> Prop
    isNull (N)      = true
    isNull (C x xs) = false           @-}
\end{code}

<br>

<div class="fragment">

\begin{code} LiquidHaskell **strengthens** data constructors
data L a where 
  N :: {v : L a | (isNull v)}
  C :: a -> L a -> {v:(L a) | not (isNull v)}
\end{code}

</div>

Multiple Measures
-----------------

LiquidHaskell *conjoins* data constructor types:

\begin{code} <br>
data L a where 
  N :: {v:L a |  (llen v) = 0 
              && (isNull v) }
  C :: a 
    -> xs:L a 
    -> {v:L a |  (llen v) = 1 + (llen xs) 
              && not (isNull v)          }
\end{code}

Multiple Measures
-----------------

Unlike [indexed types](http://dl.acm.org/citation.cfm?id=270793) ...

<br>

+ <div class="fragment">Measures *decouple* properties from structures</div>
+ <div class="fragment">Support *multiple* properties over structures </div>
+ <div class="fragment">Enable  *reuse* of structures                 </div>

<br>

<div class="fragment">Invaluable in practice!</div>

Refined Data Constructors
-------------------------

Can *directly pack* properties inside data constructors

<div class="fragment">

<br>

\begin{code}
{-@ data L a = N
             | C (x :: a) 
                 (xs :: L {v:a | x <= v})  @-}
\end{code}

</div>

<div class="fragment">

<br>

Specifies *increasing* Lists 
</div>

Refined Data Constructors
-------------------------

**Example:** Increasing Lists, with strengthened constructors:

\begin{code} <br>
data L a where
  N :: L a
  C :: x:a -> xs: L {v:a | x <= v} -> L a
\end{code}

<br>

- <div class="fragment">LiquidHaskell *checks* property when *folding* `C`</div>
- <div class="fragment">LiquidHaskell *assumes* property when *unfolding* `C`</div>

Refined Data Constructors
-------------------------

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellInsertSort.hs" target= "_blank">Demo: Insertion Sort</a> (hover for inferred types) 

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

1. **Refinements:** Types + Predicates
2. **Subtyping:** SMT Implication
3. <div class="fragment">**Measures:** Strengthened Constructors</div>
    - <div class="fragment">*Decouple* structure & property, enable *reuse*</div>

