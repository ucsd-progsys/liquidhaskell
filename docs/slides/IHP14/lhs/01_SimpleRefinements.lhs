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


Example: Integers equal to `0`
------------------------------

<br>

\begin{code}
{-@ type Zero = {v:Int | v = 0} @-}

{-@ zero :: Zero @-}
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
e := x, y, z,...    -- variable
   | 0, 1, 2,...    -- constant
   | (e + e)        -- addition
   | (e - e)        -- subtraction
   | (c * e)        -- linear multiplication
   | (f e1 ... en)  -- uninterpreted function
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


<br>

\begin{code}<div/>
b := Int 
   | Bool 
   | ...         -- base types
   | a, b, c     -- type variables

t := {x:b | p}   -- refined base 
   | x:t -> t    -- refined function  
\end{code}


Subtyping Judgment 
------------------

<br>

$$\boxed{\Gamma \vdash t_1 \preceq t_2}$$

<div class="fragment">

<br>

Where **environment** $\Gamma$ is a sequence of binders

<br>

$$\Gamma \defeq \overline{\bindx{x_i}{t_i}}$$

</div>

Subtyping is Implication
------------------------

[PVS' Predicate Subtyping](http://pvs.csl.sri.com/papers/subtypes98/tse98.pdf)

<br>

(For **Base** Types ...)




Subtyping is Implication
------------------------

<br>

$$
\begin{array}{rl}
{\mathbf{If\ VC\ is\ Valid}}   & \bigwedge_i P_i \Rightarrow  Q  \Rightarrow R \\
                & \\
{\mathbf{Then}} & \overline{\bindx{x_i}{P_i}} \vdash \reft{v}{b}{Q} \subty \reft{v}{v}{R} \\
\end{array}
$$ 


Example: Natural Numbers
------------------------

<br>

\begin{code} .  
        type Nat = {v:Int | 0 <= v}
\end{code}

<br>

<div class="fragment">

$$
\begin{array}{rcrccl}
\mathbf{By\ SMT:} & \True     & \Rightarrow &  v = 0   & \Rightarrow &  0 \leq v \\
%                &           &             &          &             &           \\
\mathbf{So:}      & \emptyset & \vdash      & \Zero  & \subty      & \Nat      \\
\end{array}
$$
</div>

<br>

<div class="fragment">

Hence, we can type:

\begin{code}
{-@ zero' :: Nat @-}
zero'     =  zero   -- zero :: Zero <: Nat
\end{code}
</div>

Contracts: Function Types
=========================

 {#as}
------

Pre-Conditions
--------------

<br>

\begin{code}
safeDiv n d = n `div` d
\end{code}

<br>

<div class="fragment">
Require non-zero input divisor `d`

\begin{code}
{-@ type NonZero = {v:Int | v /= 0} @-}
\end{code}
</div>

<br>


<div class="fragment">
Specify pre-condition as **input type** 

\begin{code}
{-@ safeDiv :: n:Int -> d:NonZero -> Int @-}
\end{code}

</div>


Example: `safeDiv`
------------------

<br>

+ **Pre-condition** divisor is *non-zero*.
+ **Input type** specifies *pre-condition*

<br>

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
{-@ abs       :: x:Int -> {v:Nat | x <= v} @-}
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
<br>
<br>

\begin{code}
data L a = N          -- Empty 
         | C a (L a)  -- Cons 
\end{code}

<br>

<div class="fragment">

How to **specify** every element in `nats` is non-negative?

\begin{code}
nats     =  0 `C` 1 `C` 3 `C` N
\end{code}
</div>


Example: Lists
--------------

How to **specify** every element in `nats` is non-negative?

\begin{code} <div/>
nats     =  0 `C` 1 `C` 2 `C` N
\end{code}

**Logic**

$$\forall x \in \mathtt{nats}. 0 \leq x$$

+ <div class="fragment">Verification: Implications over **quantified formulas**</div>
+ <div class="fragment">Quantified formulas not efficiently decidable by SMT</div>
+ <div class="fragment">**Verification** is brittle</div>


Example: Lists
--------------

How to **specify** every element in `nats` is non-negative?

\begin{code} <div/>
nats     =  0 `C` 1 `C` 2 `C` N
\end{code}

**Types + Logic**

\begin{code}
{-@ nats :: L Nat @-}
\end{code}

+ <div class="fragment">Type *implicitly* has quantification</div>
+ <div class="fragment">Sub-typing *eliminates* quantifiers</div>
+ <div class="fragment">Robust verification via efficiently decidable *quantifier-free* formulas</div>

Example: Lists
--------------

How to **verify** ? 

\begin{code} <div/>
{-@ nats :: L Nat @-}
nats     = l0
  where
    l0   = 0 `C` l1     -- Nat `C` L Nat ~~> L Nat
    l1   = 1 `C` l2     -- Nat `C` L Nat ~~> L Nat
    l2   = 2 `C` l3     -- Nat `C` L Nat ~~> L Nat  
    l3   = N            -- L Nat
\end{code}

<br>

<div class="fragment">

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo:</a> 
What if `nats` contained `-2`? 

</div>

<!--

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

-->


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
         | otherwise = N
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


