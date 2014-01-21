Termination {#termination}
==========================

Dependent != Refinement
-----------------------

<div class="fragment">**Dependent Types**</div>

+ <div class="fragment">*Arbitrary terms* appear inside types</div> 
+ <div class="fragment">Termination ensures well-defined</div>

<br>

<div class="fragment">**Refinement Types**</div>

+ <div class="fragment">*Restricted refinements* appear in types</div>
+ <div class="fragment">Termination hitherto *not* required ...</div> 
+ <div class="fragment">... except, alas, with *lazy* evaluation!</div>

Refinements Need Termination
----------------------------

<div class="fragment">
Fortunately, we can ensure termination *using refinements*
</div>


Termination Using Refinements 
-----------------------------

<a href="http://goto.ucsd.edu:8090/index.html#?demo=GCD.hs" target="_blank">Demo:</a>Lets see some simple examples.

\begin{code}
module Termination where

fibOk  :: Int -> Int
fibBad :: Int -> Int

{-@ fibBad    :: Int -> Int @-}
fibBad 0      = 1
fibBad 1      = 1
fibBad n      = fibBad (n-1) + fibBad (n-2)

{-@ fibOk :: Nat -> Nat @-}
fibOk n 
  | n <= 1    = 1
  | otherwise = fibOk (n-1) + fibOk (n-2)
\end{code}


