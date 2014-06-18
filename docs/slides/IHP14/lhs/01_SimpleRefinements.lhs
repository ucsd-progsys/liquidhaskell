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


Ex: `Int`egers equal to `0`
---------------------------

<br>

\begin{code}
{-@ type EqZero = {v:Int | v = 0} @-}

{-@ zero :: EqZero @-}
zero     =  0
\end{code}

<br>

<div class="fragment">
Refinement types via special comments `{-@ ... @-}` 

<br>

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo</a> 
</div>



Refinements Are Predicates
==========================

From A Decidable Logic
----------------------

1. Expressions

2. Predicates


Expressions
-----------

<br>

\begin{code} <div/> 
e := x, y, z,...      -- variable
   | 0, 1, 2,...      -- constant
   | (e + e)          -- addition
   | (e - e)          -- subtraction
   | (c * e)          -- linear multiplication
   | (f e1 e2 ... en) -- uninterpreted function
\end{code}

Predicates
----------

<br>

\begin{code} <div/>
p := e           -- atom 
   | e1 == e2    -- equality
   | e1 <  e2    -- ordering 
   | (p && p)    -- and
   | (p || p)    -- or
   | (not p)     -- negation
\end{code}

Refinement Types
----------------



\begin{code}<div/>
b := Int 
   | Bool 
   | ...         -- base types
   | a, b, c     -- type variables

t := {x:b | p}   -- refined base type 
   | x:t -> t    -- dependent function 
\end{code}


Subtyping Judgment 
------------------

$$\boxed{\Gamma \vdash t_1 \preceq t_2}$$

<div class="fragment">

Where **environment** is *sequence* of binders

$$\Gamma \defeq \overline{\bindx{x_i}{t_i}}$$

</div>

Subtyping Is Implication
------------------------

[PVS' Predicate Subtyping](http://pvs.csl.sri.com/papers/subtypes98/tse98.pdf)

<br>

(For **Base** Types...)


Subtyping is Implication
------------------------

<br>
<br>

$$
\inferrule[]
          {\forall x_i, v. \wedge_i p_i \Rightarrow p_1 \Rightarrow p_2}
          {\bind{x_i}{t_i} \vdash \reft{v}{b}{p_1} \preceq \reft{v}{b}{p_2}} 
$$

$$
\begin{array}{rrrcl}
{\mathbf{If}}   & \vdash & P              & \Rightarrow & Q              \\
                &        &                &             &                \\
{\mathbf{Then}} & \vdash & \reft{v}{\Int}{P} & \preceq & \reft{v}{\Int}{Q} \\
\end{array}
$$ 


{x1:P1},...,{xn:Pn} |- {v:t|P} <: 
<!-- 

Subtyping is Implication
------------------------


<br>
<br>

---------   ------------   --------------------------   
  **If:**            `P`   `=> Q` 
            
**Then:**    `{v:t | P}`   `<: {v:t | Q}`
---------   ------------   --------------------------   

-->


Example: Natural Numbers
------------------------

\begin{code} <div/> 
        type Nat = {v:Int | 0 <= v}
\end{code}

<br>

<div class="fragment">

-------------    ---------  ----------------
  **By SMT:**      `v = 0`  `=>`  `0 <= v` 
             
      **So:**     `EqZero`  `<:`  `Nat`
-------------    ---------  ----------------

</div>

<br>

<div class="fragment">

Hence, we can type:

\begin{code}
{-@ zero' :: Nat @-}
zero'     =  zero   -- zero :: EqZero <: Nat
\end{code}
</div>

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

\begin{code}
{-@ type Even = {v:Int | v mod 2 =  0} @-}
{-@ type Odd  = {v:Int | v mod 2 /= 0} @-}
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



Contracts: Function Types
=========================

 {#as}
------

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

<br>

Outputs **refer to** inputs

<br>

**Relational** invariants


Dependent Function Types
========================

Example: `range`
----------------

`(range i j)` returns `Int`s **between** `i` and `j`


Example: `range`
----------------

`(range i j)` returns `Int`s **between** `i` and `j`

<br>

\begin{code}
{-@ type Btwn I J = {v:_ | (I<=v && v<J)} @-}
\end{code}


Example: `range`
----------------

`(range i j)` returns `Int`s between `i` and `j`

<br>

\begin{code}
{-@ range :: i:Int -> j:Int -> L (Btwn i j) @-}
range i j            = go i
  where
    go n | n < j     = n `C` go (n + 1)  
         | otherwise =  N
\end{code}

<br>

<div class="fragment">
**Note:** Type of `go` is automatically inferred
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

<div class="fragment">To ensure safety, *require* `i` between `0` and list **length**</div>

<br>

<div class="fragment">Need way to **measure** the length of a list [[continue...]](02_Measures.lhs.slides.html)</div>


