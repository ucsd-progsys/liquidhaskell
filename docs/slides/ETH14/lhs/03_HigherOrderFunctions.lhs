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

Higher-Order Specifications
---------------------------

Types scale to *Higher-Order* Specifications

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
listSum     :: [Int] -> Int
listSum xs  = loop 0 n 0 body 
  where 
    body    = \i acc -> acc + (xs !! i)
    n       = length xs
\end{code}

<br>

<div class="fragment">
**Function Subtyping** 

+ `body` called with `i :: Btwn 0 (llen xs)`

+ Hence, indexing with `!!` is safe.
</div>

<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=Loop.hs" target= "_blank">Demo:</a> Tweak `loop` exit condition? 
</div>

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
\begin{code} Recall 
foldl :: (α -> β -> α) -> α -> [β] -> α
\end{code}
</div>

<br>

<div class="fragment">
How to **instantiate** `α` and `β` ?
</div>

Function Subtyping
------------------

\begin{code}<div/>
(+) ::  x:Int -> y:Int -> {v:Int|v=x+y} 
    <:  Nat   -> Nat   -> Nat
\end{code}

<br>

<div class="fragment">
Because,

\begin{code}<div/>
               |- Nat       <: Int  -- Contra
  x:Nat, y:Nat |- {v = x+y} <: Nat  -- Co
\end{code}
</div>

<br>

<div class="fragment">
Because,

\begin{code}<div/>
  0<=x && 0<=y && v = x+y   => 0 <= v
\end{code}
</div>

Example: Summing `Nat`s
-----------------------

\begin{code} <div/> 
{-@ sumNats :: [Nat] -> Nat @-}
sumNats xs  = foldl (+) 0 xs 
\end{code}

<br>

\begin{code} Where:
foldl :: (α -> β -> α) -> α -> [β] -> α
(+)   :: Nat -> Nat -> Nat
\end{code}

<br>

<div class="fragment">
Hence, `sumNats` verified by **instantiating** `α,β := Nat`
</div>

<br>

<div class="fragment">
`α` is **loop invariant**, instantiation is invariant **synthesis**
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
Abstract interpretatn. to get solution for $\kvar{}$
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

