 {#laziness}
============

<div class="hidden">
\begin{code}
module Laziness where

import Language.Haskell.Liquid.Prelude

{-@ LIQUID "--no-termination" @-}

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
{-@ safeDiv :: _ -> {v:_ |v /= 0} -> Int @-}
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

\begin{spec}
{-@ foo       :: n:Nat -> {v:Nat | v < n} @-}
foo n   
  | n > 0     = n - 1
  | otherwise = foo n
\end{spec}

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
              (\x -> 2014 `safeDiv` z) a 
\end{code}

<br>

<div class="fragment">
Why is this program **deemed safe**?! 
</div>


*Is Safe* With Eager Eval
-------------------------

\begin{spec}
{-@ foo       :: n:Nat -> {v:Nat | v < n} @-}
foo n   
  | n > 0     = n - 1
  | otherwise = foo n

explode = let z = 0     -- :: {v:Int| v = 0}
              a = foo z -- :: {v:Nat| v < z}
          in  
              (\x -> 2014 `safeDiv` z) a 
\end{spec}

<br>

**Safe** in Java, ML: program **never hits** divide-by-zero 

*Unsafe* With Lazy Eval
-----------------------

\begin{spec} <div/>
{-@ foo       :: n:Nat -> {v:Nat | v < n} @-}
foo n   
  | n > 0     = n - 1
  | otherwise = foo n

explode = let z = 0     -- :: {v:Int| v = 0}
              a = foo z -- :: {v:Nat| v < z}
          in  
              (\x -> 2014 `safeDiv` z) a 
\end{spec}

<br>

**Unsafe** in Haskell: skips `foo z` **hits** divide-by-zero!

Problem: Divergence
-------------------

What is denoted by:

$$ e :: \reft{v}{\Int}{p}$$

<br>

<div class="fragment">
$e$ evaluates to $\Int$ that satisfies $p$  
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

\begin{spec} **Consider** <div/> 
        {-@ e :: {v : Int | P} @-}

        let x = e in body 
\end{spec}

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

\begin{spec} 
{-@ foo       :: n:Nat -> {v:Nat | v < n} @-}
foo n   
  | n > 0     = n - 1
  | otherwise = foo n

explode = let z = 0     -- :: {v:Int| v = 0}
              a = foo z -- :: {v:Nat| v < z}
          in  
              (\x -> 2014 `safeDiv` z) a 
\end{spec}

<br>

Inconsistent `a` is sound for **eager**, unsound for **lazy**


Panic! Now what?
---------------

<div class="fragment">
**Solution** 

Assign *non-trivial* refinements to *non-diverging* terms!
</div>

<br>

<div class="fragment">
**Harder Problem?**

Yikes, doesn't non-divergence mean tracking *permination?*
</div>

<br>

<div class="fragment">
**Relax**

Its *easy* ... since we have *refinements*! [[continue...]](10_Termination.lhs.slides.html)
</div>

<br>



