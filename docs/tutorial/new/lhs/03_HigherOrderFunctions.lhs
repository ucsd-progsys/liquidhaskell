  {#hofs}
=========

<div class="hidden">
\begin{code}
module Loop (
    listSum
  , listNatSum
  , listEvenSum
  ) where

import Prelude

{-@ LIQUID "--no-termination"@-}
listNatSum  :: [Int] -> Int
listEvenSum :: [Int] -> Int
add         :: Int -> Int -> Int
\end{code}
</div>

Higher-Order Specifications
---------------------------

Types yield easy *Higher-Order* Specifications

<br>

+ <div class="fragment">map</div>
+ <div class="fragment">fold</div>
+ <div class="fragment">visitors</div>
+ <div class="fragment">callbacks</div>
+ <div class="fragment">...</div>

<br>

<div class="fragment">Difficult with first-order program logics</div>


Higher Order Specifications
===========================

Example: Higher Order Loop
--------------------------

\begin{code}
loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f = go lo base
  where 
    go i acc 
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc
\end{code}

<br>

LiquidHaskell infers `f` called with values `(Btwn lo hi)`


Example: Summing a List
-----------------------

\begin{code}
listSum xs  = loop 0 n 0 body 
  where 
    body    = \i acc -> acc + (xs !! i)
    n       = length xs
\end{code}

<br>

<div class="fragment">
By *function subtyping* LiquidHaskell infers:
</div>

- <div class="fragment">`body` called with `Btwn 0 (llen xs)`</div> 
- <div class="fragment">hence, indexing with `!!` is safe.</div>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=Loop.hs" target= "_blank">Demo:</a> Tweak `loop` exit condition? 
</div>

Example: Summing a `Nat` List
-----------------------------

<br>

\begin{code}
{-@ listNatSum :: [Nat] -> Nat @-}
listNatSum xs  = loop 0 n 0 body 
  where 
    body       = \i acc -> acc + (xs !! i)
    n          = length xs
\end{code}


LiquidHaskell infers that `(+)` has type

+ `x:Int-> y:Int -> {v:Int| v=x+y} <: Nat -> Nat -> Nat`

At callsite, LiquidHaskell *instantiates* `a` in `loop` with `Nat`:

+ `loop :: Int -> Int -> Nat -> (Int -> Nat -> Nat) -> Nat`

Yielding the output.


Example: Summing an `Even` List
-------------------------------

<br>

\begin{code}
{-@ listEvenSum :: [Even] -> Even @-}
listEvenSum xs  = loop 0 n 0 body 
  where 
    body        = \i acc -> acc + (xs !! i)
    n           = length xs
\end{code}

LiquidHaskell infers that `(+)` has type

- `x:Int-> y:Int -> {v:Int| v=x+y} <: Even -> Even -> Even`

At callsite, LiquidHaskell *instantiates* `a` in `loop` with `Nat`:

- `loop :: Int -> Int -> Even -> (Int -> Even -> Even) -> Even`

Yielding the output.

Index-Dependent Loop Invariant
------------------------------

Cannot use parametric polymorphism to verify:

<br>

\begin{code}
{-@ add :: n:Nat -> m:Nat -> {v:Int| v = m + n} @-}
add n m = loop 0 m n (\_ i -> i + 1)
\end{code}

- Cannot instantiate `a` with `{v:Int|v = n + m}` ... 
- ... as this only holds after **last iteration** of loop!

**Problem** Require Higher Order Invariants

- On values computed in **intermediate** iterations...
- ... i.e. invariants that **depend on the iteration index**.

