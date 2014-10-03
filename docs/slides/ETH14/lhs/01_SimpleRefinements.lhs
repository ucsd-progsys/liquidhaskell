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

<br> 

1. Expressions

2. Predicates

<br>

<div class="fragment">

**Refinement Logic: QF-UFLIA**

Quant.-Free. Uninterpreted Functions and Linear Arithmetic 

</div>


Expressions
-----------

<br>

\begin{spec} <div/> 
e := x, y, z,...    -- variable
   | 0, 1, 2,...    -- constant
   | (e + e)        -- addition
   | (e - e)        -- subtraction
   | (c * e)        -- linear multiplication
   | (f e1 ... en)  -- uninterpreted function
\end{spec}

Predicates
----------

<br>

\begin{spec} <div/>
p := e           -- atom 
   | e1 == e2    -- equality
   | e1 <  e2    -- ordering 
   | (p && p)    -- and
   | (p || p)    -- or
   | (not p)     -- negation
\end{spec}

<br>


Refinement Types
----------------


<br>

\begin{spec}<div/>
b := Int 
   | Bool 
   | ...         -- base types
   | a, b, c     -- type variables

t := {x:b | p}   -- refined base 
   | x:t -> t    -- refined function  
\end{spec}


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

<br>

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

\begin{spec} <div/>  
        type Nat = {v:Int | 0 <= v}
\end{spec}

<br>

<div class="fragment">

$$
\begin{array}{rcrccll}
\mathbf{VC\ is\ Valid:} & \True     & \Rightarrow &  v = 0   & \Rightarrow &  0 \leq v & \mbox{(by SMT)} \\
%                &           &             &          &             &           \\
\mathbf{So:}      & \emptyset & \vdash      & \Zero  & \subty      & \Nat   &   \\
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
safeDiv n d = n `div` d   -- crashes if d==0
\end{code}

<br>

<div class="fragment">
**Requires** non-zero input divisor `d`

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


Precondition: `safeDiv`
-----------------------

Specify pre-condition as **input type** 

\begin{spec} <div/>
{-@ safeDiv :: n:Int -> d:NonZero -> Int @-}
\end{spec}

<br>

Precondition is checked at **call-site**

\begin{code}
{-@ bad :: Nat -> Int @-}
bad n   = 10 `safeDiv` n
\end{code}

<br>

<div class="fragment">
**Rejected As** 

$$\bindx{n}{\Nat} \vdash \reftx{v}{v = n} \not \subty \reftx{v}{v \not = 0}$$

</div>

Precondition: `safeDiv`
-----------------------

Specify pre-condition as **input type** 

\begin{spec} <div/>
{-@ safeDiv :: n:Int -> d:NonZero -> Int @-}
\end{spec}


<br>

Precondition is checked at **call-site**

\begin{code}
{-@ ok  :: Nat -> Int @-}
ok n    = 10 `safeDiv` (n+1)
\end{code}

<br>

<div class="fragment">
**Verifies As** 

$\bindx{n}{\Nat} \vdash \reftx{v}{v = n+1} \subty \reftx{v}{v \not = 0}$
</div>

Precondition: `safeDiv`
-----------------------

Specify pre-condition as **input type** 

\begin{spec} <div/>
{-@ safeDiv :: n:Int -> d:NonZero -> Int @-}
\end{spec}

<br>

Precondition is checked at **call-site**

\begin{spec} <div/>
{-@ ok  :: Nat -> Int @-}
ok n    = 10 `safeDiv` (n+1)
\end{spec}

<br>

**Verifies As**

$$(0 \leq n) \Rightarrow (v = n+1) \Rightarrow (v \not = 0)$$



Post-Conditions
---------------

**Ensures** output is a `Nat` greater than input `x`.

\begin{code}
abs x | 0 <= x    = x 
      | otherwise = 0 - x
\end{code}

<br>

<div class="fragment">
Specify post-condition as **output type**

\begin{code}
{-@ abs :: x:Int -> {v:Nat | x <= v} @-}
\end{code}
</div>

<br>

<div class="fragment">
**Dependent Function Types**

Outputs *refer to* inputs
</div>

Postcondition: `abs`
--------------------

Specify post-condition as **output type** 

\begin{spec} <div/>
{-@ abs :: x:Int -> {v:Nat | x <= v} @-}
abs x | 0 <= x    = x 
      | otherwise = 0 - x
\end{spec}

<br>

Postcondition is checked at **return-site**

<br>

Postcondition: `abs`
--------------------

Specify post-condition as **output type** 

\begin{spec} <div/>
{-@ abs :: x:Int -> {v:Nat | x <= v} @-}
abs x | 0 <= x    = x 
      | otherwise = 0 - x
\end{spec}

<br>

**Verified As**

<br>

$$\begin{array}{rll}
\bindx{x}{\Int},\bindx{\_}{0 \leq x}      & \vdash \reftx{v}{v = x}     & \subty \reftx{v}{0 \leq v \wedge x \leq v} \\
\bindx{x}{\Int},\bindx{\_}{0 \not \leq x} & \vdash \reftx{v}{v = 0 - x} & \subty \reftx{v}{0 \leq v \wedge x \leq v} \\
\end{array}$$

Postcondition: `abs`
--------------------

Specify post-condition as **output type** 

\begin{spec} <div/>
{-@ abs :: x:Int -> {v:Nat | x <= v} @-}
abs x | 0 <= x    = x 
      | otherwise = 0 - x
\end{spec}

<br>

**Verified As**

<br>

$$\begin{array}{rll}
(0 \leq x)      & \Rightarrow (v = x)     & \Rightarrow (0 \leq v \wedge x \leq v) \\
(0 \not \leq x) & \Rightarrow (v = 0 - x) & \Rightarrow (0 \leq v \wedge x \leq v) \\
\end{array}$$


 {#inference}
=============

From Checking To Inference
--------------------------

<br>
<br>

**So far**

How to **check** code against given signature

<br>

<div class="fragment">

**Next**

How to **infer** signatures from code

</div>

From Checking To Inference
--------------------------

<br>
<br>


**2-Phase Process**

<div class="fragment">

<br>

1. Hindley-Milner infers **types**
2. Abstract Interpr. infers **refinements**  

</div>

<br>

<div class="fragment">Lets quickly look at 2. </div>



From Checking To Inference
==========================


Recipe
------

<br>

<div class="fragment">

**Step 1. Templates**

Types with variables $\kvar{}$ for *unknown* refinements

</div>

<br>

<div class="fragment">

**Step 2. Constraints**

Typecheck templates: VCs $\rightarrow$ Horn *constraints* over $\kvar{}$

</div>

<br>

<div class="fragment">

**Step 3. Solve**

Via *least-fixpoint* over suitable abstract domain

</div>

Step 1. Templates (`abs`)
-------------------------

<br>

<div class="fragment">
**Type**

$$\bindx{x}{\Int} \rightarrow \Int$$
</div>

<br>

<div class="fragment">
**Template**

$$\ereft{x}{\Int}{\kvar{1}} \rightarrow \reft{v}{\Int}{\kvar{2}}$$
</div>

Step 2. Constraints (`abs`)
-------------------------

<br>

Step 2. Constraints (`abs`)
-------------------------

<br>

**Subtyping Queries**

<br>

$$
\begin{array}{rll}
\bindx{x}{\kvar{1}},\bindx{\_}{0 \leq x}      & \vdash \reftx{v}{v = x}     & \subty \reftx{v}{\kvar{2}} \\
\bindx{x}{\kvar{1}},\bindx{\_}{0 \not \leq x} & \vdash \reftx{v}{v = 0 - x} & \subty \reftx{v}{\kvar{2}} \\
\end{array}
$$

Step 2. Constraints (`abs`)
-------------------------

<br>

**Verification Conditions**

<br>

$$\begin{array}{rll}
{\kvar{1}} \wedge (0 \leq x)      & \Rightarrow (v = x)     & \Rightarrow \kvar{2} \\
{\kvar{1}} \wedge (0 \not \leq x) & \Rightarrow (v = 0 - x) & \Rightarrow \kvar{2} \\
\end{array}$$


Step 2. Constraints (`abs`)
-------------------------

<br>

**Horn Constraints** over $\kvar{}$

<br>

$$\begin{array}{rll}
{\kvar{1}} \wedge (0 \leq x)      & \Rightarrow (v = x)     & \Rightarrow \kvar{2} \\
{\kvar{1}} \wedge (0 \not \leq x) & \Rightarrow (v = 0 - x) & \Rightarrow \kvar{2} \\
\end{array}$$

<br>
<br>

**Note:** $\kvar{}$ occur positively, hence constraints are monotone.

Step 3. Solve (`abs`)
---------------------

<br>

Least-fixpoint over abstract domain 

<br>

Step 3. Solve (`abs`)
---------------------

**Predicate Abstraction**

Conjunction of predicates from (finite) ground set $\quals$

<br>

<div class="fragment">
$$\mbox{e.g.}\ \quals \defeq \{ c \sim X \}$$

<br>

$$\begin{array}{ccll}
  c     & \in & \{0,1,\ldots   \}                & \mbox{program constants} \\
  X     & \in & \{n,x,v,\ldots \}                & \mbox{program variables} \\
  \sim  & \in & \{<, \leq, >, \geq, =, \not =\}  & \mbox{comparisons}       \\
  \end{array}$$

</div>

Step 3. Solve (`abs`)
---------------------

Least-fixpoint over abstract domain 

<br>

**Predicate Abstraction**

Conjunction of predicates from (finite) ground set $\quals$

<br>

+ Obtain $\quals$ via CEGAR
+ Or use other domains

<br>

[[Houdini](http://dl.acm.org/citation.cfm?id=730008), [HMC](http://goto.ucsd.edu/~rjhala/papers/hmc.html)]


Recipe Scales Up
----------------

<br>

**1. Templates** $\rightarrow$ **2. Horn Constraints** $\rightarrow$ **3. Fixpoint**

<br>

<div class="fragment">
+ Define type *checker* and get *inference* for free 

+ Scales to Collections, HOFs, Polymorphism

</div>
<br>

<div class="fragment">
**Next:** Collections
</div>

<!--
<div class="fragment">
**Key Requirement** 

Refinements belong in abstract domain, e.g. QF-UFLIA
</div>
-->


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

<br>

How to **specify** every element in `nats` is non-negative?

\begin{spec} 
nats     =  0 `C` 1 `C` 2 `C` N
\end{spec}

<br>

**Logic**

$$\forall x \in \mathtt{nats}. 0 \leq x$$

<br>

<div class="fragment">
VCs over **quantified formulas** ... *challenging* for SMT
</div>


Example: Lists
--------------

<br>

How to **specify** every element in `nats` is non-negative?

\begin{spec} 
nats     =  0 `C` 1 `C` 2 `C` N
\end{spec}

<br>

**Refinement Types**

\begin{code}
{-@ nats :: L Nat @-}
\end{code}

<br>

+ <div class="fragment">Type *implicitly* has quantification</div>
+ <div class="fragment">Sub-typing *eliminates* quantifiers</div>
+ <div class="fragment">Robust verification via *quantifier-free* VCs</div>

Example: Lists
--------------

How to **verify** ? 

\begin{spec} <div/>
{-@ nats :: L Nat @-}
nats   = l0
  where
    l0 = 0 `C` l1  -- Nat `C` L Nat >>> L Nat
    l1 = 1 `C` l2  -- Nat `C` L Nat >>> L Nat
    l2 = 2 `C` l3  -- Nat `C` L Nat >>> L Nat
    l3 = N         -- L Nat
\end{spec}

<br>

Example: `range`
----------------

`(range i j)` returns `Int`s **between** `i` and `j`


Example: `range`
----------------

`(range i j)` returns `Int`s **between** `i` and `j`

<br>

\begin{code}
{-@ type Btwn I J = { v:_ | I<=v && v<J } @-}
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


