 {#laziness}
============

<div class="hidden">
\begin{code}
module Laziness where

import Language.Haskell.Liquid.Prelude

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short"          @-}


safeDiv :: Int -> Int -> Int
foo     :: Int -> Int
-- zero    :: Int 
-- diverge :: a -> b
\end{code}
</div>


Lazy Evaluation?
----------------

Lazy Evaluation
===============

SMT based Verification
----------------------

Techniques developed for **strict** languages

<br>

<div class="fragment">

-----------------------   ---   ------------------------------------------
        **Floyd-Hoare**    :    `ESCJava`, `SpecSharp` ...
     **Model Checkers**    :    `Slam`, `Blast` ...
   **Refinement Types**    :    `DML`, `Stardust`, `Sage`, `F7`, `F*`, ...
-----------------------   ---   ------------------------------------------

</div>

<br>

<div class="fragment">
Surely soundness carries over to Haskell, right?
</div>


Back To the Beginning
---------------------

\begin{code}
{-@ safeDiv :: Int -> {v:Int| v /= 0} -> Int @-}
safeDiv n 0 = liquidError "div-by-zero!"
safeDiv n d = n `div` d
\end{code}

<br>

<div class="fragment">
Should only call `safeDiv` with **non-zero** values
</div>

An Innocent Function
--------------------

`foo` returns a value **strictly less than** input.

<br>

\begin{code} <div/>
{-@ foo       :: n:Nat -> {v:Nat | v < n} @-}
foo n   
  | n > 0     = n - 1
  | otherwise = foo n
\end{code}

LiquidHaskell Lies! 
-------------------

\begin{code}
{-@ foo       :: n:Nat -> {v:Nat | v < n} @-}
foo n   
  | n > 0     = n - 1
  | otherwise = foo n

explode = let z = 0    
              a = foo z
          in  
              (\x -> 2013 `safeDiv` z) a 
\end{code}

<br>

<div class="fragment">
Why is this program **deemed safe**?! 
</div>


*Safe* With Eager Eval
----------------------

\begin{code} <div/>
{-@ foo       :: n:Nat -> {v:Nat | v < n} @-}
foo n   
  | n > 0     = n - 1
  | otherwise = foo n

explode = let z = 0     -- :: {v:Int| v = 0}
              a = foo z -- :: {v:Nat| v < z}
          in  
              (\x -> 2013 `safeDiv` z) a 
\end{code}

<br>

<div class="fragment">
**Safe** in Java, ML: program spins away, **never hits** divide-by-zero 
</div>

*Unsafe* With Lazy Eval
-----------------------

\begin{code} <div/>
{-@ foo       :: n:Nat -> {v:Nat | v < n} @-}
foo n   
  | n > 0     = n - 1
  | otherwise = foo n

explode = let z = 0     -- :: {v:Int| v = 0}
              a = foo z -- :: {v:Nat| v < z}
          in  
              (\x -> 2013 `safeDiv` z) a 
\end{code}

<br>

**Unsafe** in Haskell: program skips `foo z` and **hits** divide-by-zero!

Problem: Divergence
-------------------

<div class="fragment">
What is denoted by:

`e :: {v:Int | P}`

</div>

<br>

<div class="fragment">
`e` evaluates to `Int` satisfying `P`  
</div>

<div class="fragment">
or

**diverges**! 
</div>

<div class="fragment">
<br>

Classical Floyd-Hoare notion of [partial correctness](http://en.wikipedia.org/wiki/Hoare_logic#Partial_and_total_correctness)

</div>



Problem: Divergence
-------------------

\begin{code} **Consider** <div/> 
        {-@ e :: {v : Int | P} @-}

        let x = e in body 
\end{code}

<br>

<div class="fragment">
**Eager Evaluation** 

*Can* assume `P(x)` when checking `body`
</div>

<br>

<div class="fragment">
**Lazy Evaluation** 

*Cannot* assume `P(x)` when checking `body`
</div>

Eager vs. Lazy Binders 
----------------------

\begin{code} <div/>
{-@ foo       :: n:Nat -> {v:Nat | v < n} @-}
foo n   
  | n > 0     = n - 1
  | otherwise = foo n

explode = let z = 0     -- :: {v:Int| v = 0}
              a = foo z -- :: {v:Nat| v < z}
          in  
              (\x -> 2013 `safeDiv` z) a 
\end{code}

<br>

Inconsistent refinement for `a` is sound for **eager**, unsound for **lazy**


Panic! Now what?
---------------

<div class="fragment">
**Solution** 

Assign *non-trivial* refinements to *non-diverging* terms!
</div>

<br>

<div class="fragment">

**Require A Termination Analysis**

Don't worry, its easy...

</div>

<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=TellingLies.hs" target="_blank">Demo:</a> &nbsp; Disable `"--no-termination"` and see what happens!
</div>

Recap
-----

1. Refinements: Types + Predicates
2. Subtyping: SMT Implication
3. Measures: Strengthened Constructors
4. Abstract: Refinements over functions and data
5. **Lazy Evaluation:** Requires Termination
6. <div class="fragment">**Termination:** via Refinements!</div>

<br>
<br>

<div class="fragment">[[continue...]](10_Termination.lhs.slides.html)</div>


