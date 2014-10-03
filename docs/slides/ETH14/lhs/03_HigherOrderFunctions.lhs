  {#hofs}
=========

<div class="hidden">
\begin{code}
module Loop (
    listSum
  , sumNats
  ) where

import Prelude

{-@ LIQUID "--no-termination"@-}
sumNats  :: [Int] -> Int
add         :: Int -> Int -> Int
\end{code}
</div>

Higher-Order Functions 
----------------------

Types scale to *Higher-Order Functions*  

<br>

<div class="fragment">

+ map
+ fold
+ visitors
+ callbacks
+ ...

</div>

<br>

<div class="fragment">Very difficult with *first-order program logics*</div>


Higher Order Specifications 
===========================

Example: Higher Order Loop
--------------------------

<br>

\begin{code}
loop :: Int -> Int -> α -> (Int -> α -> α) -> α
loop lo hi base f = go lo base
  where 
    go i acc 
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc
\end{code}

<br>

By subtyping, we infer `f` called with values `(Btwn lo hi)`


Example: Summing Lists
----------------------

\begin{code}
listSum xs     = loop 0 n 0 body 
  where 
    body i acc = acc + (xs !! i)
    n          = length xs
\end{code}

<br>

<div class="fragment">
**Function Subtyping** 

\begin{spec}
loop :: l -> h -> α -> (Btwn l h -> α -> α) -> α
\end{spec}
</div>

<br>

<div class="fragment">
At callsite, since `l := 0` and `h := llen xs` 

\begin{spec}
body :: Btwn 0 (llen xs) -> Int -> Int
\end{spec}
</div>

Example: Summing Lists
----------------------

\begin{spec}
listSum xs     = loop 0 n 0 body 
  where 
    body i acc = acc + (xs !! i)
    n          = length xs
\end{spec}

<br>

**Function Subtyping** 

\begin{spec}
body :: Btwn 0 (llen xs) -> Int -> Int
\end{spec}

<br>

So `i` is `Btwn 0 (llen xs)`; indexing `!!` is verified safe.


Polymorphic Instantiation
=========================

 {#poly}
--------

Example: Summing `Nat`s
-----------------------

\begin{code}
{-@ sumNats :: [Nat] -> Nat @-}
sumNats xs  = foldl (+) 0 xs 
\end{code}

<br>

<div class="fragment">
\begin{spec} Recall 
foldl :: (α -> β -> α) -> α -> [β] -> α
\end{spec}
</div>

<br>

<div class="fragment">
How to **instantiate** `α` and `β` ?
</div>

Function Subtyping
------------------

\begin{spec}<div/>
(+) ::  x:Int -> y:Int -> {v:Int|v=x+y} 
    <:  Nat   -> Nat   -> Nat
\end{spec}

<br>

<div class="fragment">
Because,

\begin{spec}<div/>
             |- Nat       <: Int  -- Contra (in)
x:Nat, y:Nat |- {v = x+y} <: Nat  -- Co    (out)
\end{spec}
</div>

<br>

<div class="fragment">
Because,

\begin{spec}<div/>
  0<=x && 0<=y && v = x+y   => 0 <= v
\end{spec}
</div>




Example: Summing `Nat`s
-----------------------

\begin{spec} <div/> 
{-@ sumNats :: [Nat] -> Nat @-}
sumNats xs  = foldl (+) 0 xs 
\end{spec}

<br>

\begin{spec} Where:
foldl :: (α -> β -> α) -> α -> [β] -> α
(+)   :: Nat -> Nat -> Nat
\end{spec}

<br>

<div class="fragment">
Hence, `sumNats` verified by **instantiating** `α,β := Nat`
</div>

<br>

<div class="fragment">
`α` is **loop invariant**, instantiation is invariant **inference**
</div>

Instantiation And Inference
---------------------------

Polymorphism ubiquitous, so inference is critical!

<br>

<div class="fragment">
**Step 1. Templates** 
Instantiate with unknown refinements

$$
\begin{array}{rcl}
\alpha & \defeq & \reft{v}{\Int}{\kvar{\alpha}}\\
\beta  & \defeq & \reft{v}{\Int}{\kvar{\beta}}\\
\end{array}
$$
</div>

<br>
<div class="fragment">
**Step 2. Horn-Constraints** 
By type checking the templates
</div>

<br>
<div class="fragment">
**Step 3. Fixpoint** 
Abstract interpretation to get solution for $\kvar{}$
</div>


Iteration Dependence
--------------------

**Problem:** Cannot use parametric polymorphism to verify

<br>

\begin{code}
{-@ add :: n:Nat -> m:Nat -> {v:Nat|v=m+n} @-}
add n m = loop 0 m n (\_ i -> i + 1)
\end{code}

<br>

<div class="fragment">
As property only holds after **last iteration** ...

<br>

... cannot instantiate $\alpha \defeq \reft{v}{\Int}{v = n + m}$
</div>

<br>

<div class="fragment">
**Problem:** *Iteration-dependent* invariants...? &nbsp; &nbsp; [[Continue]](04_AbstractRefinements.lhs.slides.html)
</div>

