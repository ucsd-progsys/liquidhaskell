  {#hofs}
=========

<div class="hidden">
\begin{code}
module Loop (
    listSum
  , listNatSum
  ) where

import Prelude

{-@ LIQUID "--no-termination"@-}
listNatSum  :: [Int] -> Int
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

\begin{code}
loop :: Int -> Int -> α -> (Int -> α -> α) -> α
loop lo hi base f = go lo base
  where 
    go i acc 
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc
\end{code}

<br>

LiquidHaskell infers `f` called with values `(Btwn lo hi)`


Example: Summing Lists
----------------------

\begin{code}
listSum xs  = loop 0 n 0 body 
  where 
    body    = \i acc -> acc + (xs !! i)
    n       = length xs
\end{code}

<br>

- <div class="fragment">*Function subtyping:* `body` called on `i :: Btwn 0 (llen xs)`</div>
- <div class="fragment">Hence, indexing with `!!` is safe.</div>


<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=Loop.hs" target= "_blank">Demo:</a> Tweak `loop` exit condition? 
</div>

Example: Summing `Nat`s
-----------------------

<br>

\begin{code}
{-@ listNatSum :: [Nat] -> Nat @-}
listNatSum xs  = loop 0 n 0 body 
  where 
    body       = \i acc -> acc + (xs !! i)
    n          = length xs
\end{code}

<br>

<div class="fragment" align="center">

----  ----  ---------------------------------------
 (+)  `::`  `x:Int -> y:Int -> {v:Int| v=x+y}`
      `<:`  `Nat   -> Nat   -> Nat`
----  ----  ---------------------------------------

</div>

Example: Summing `Nat`s
-----------------------

\begin{code} <br> 
{-@ listNatSum :: [Nat] -> Nat @-}
listNatSum xs  = loop 0 n 0 body 
  where 
    body       = \i acc -> acc + (xs !! i)
    n          = length xs
\end{code}

<br>

Hence, verified by *instantiating* `α` of `loop` with `Nat`

<div class="fragment">`Int -> Int -> Nat -> (Int -> Nat -> Nat) -> Nat`</div>

Example: Summing `Nat`s
-----------------------

\begin{code} <br> 
{-@ listNatSum :: [Nat] -> Nat @-}
listNatSum xs  = loop 0 n 0 body 
  where 
    body       = \i acc -> acc + (xs !! i)
    n          = length xs
\end{code}

<br>

+ Parameter `α` corresponds to *loop invariant*

+ Instantiation corresponds to invariant *synthesis*


Instantiation And Inference
---------------------------

+ <div class="fragment">Polymorphic instantiation happens *everywhere*</div> 

+ <div class="fragment">Automatic inference is crucial</div>

+ <div class="fragment">*Cannot use* unification (unlike indexed approaches)</div>

+ <div class="fragment">*Can reuse* [SMT/predicate abstraction.](http://goto.ucsd.edu/~rjhala/papers/liquid_types.html)</div>



Iteration Dependence
--------------------

**Cannot** use parametric polymorphism to verify:

<br>

\begin{code}
{-@ add :: n:Nat -> m:Nat -> {v:Nat|v=m+n} @-}
add n m = loop 0 m n (\_ i -> i + 1)
\end{code}

<br>


- <div class="fragment">As property only holds after **last** loop iteration...</div>

- <div class="fragment">... cannot instantiate `α` with `{v:Int | v = n + m}`</div>

<div class="fragment">**Problem:** Need *iteration-dependent* invariants...</div>

