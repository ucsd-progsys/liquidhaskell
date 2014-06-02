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

\begin{code}
{-@ foo       :: n:Nat -> {v:Nat | v < n} @-}
foo n   
  | n > 0     = n - 1
  | otherwise = foo n
\end{code}

LiquidHaskell Lies! 
-------------------

\begin{code}
explode = let z = 0
              a = foo z
          in  (\x -> 2013 `safeDiv` z) a 
\end{code}

<br>

<div class="fragment">
Why is this program deemed **safe**? 
</div>

<br>

<div class="fragment">
(Where's the *red* highlight when you want it?!)
</div>


Safe With Eager Eval
--------------------

\begin{code} <div/>
{- foo       :: n:Nat -> {v:Nat | v < n} -}
foo n   
  | n > 0     = n - 1
  | otherwise = foo n

explode = let z = 0
              a = foo z
          in  (\x -> 2013 `safeDiv` z) a 
\end{code}

<br>

<div class="fragment">
Java, ML *are safe*: program spins away, **never hits** divide-by-zero 
</div>

Unsafe With Lazy Eval
---------------------

\begin{code}<div/>
{- foo       :: n:Nat -> {v:Nat | v < n} -}
foo n   
  | n > 0     = n - 1
  | otherwise = foo n

explode = let z = 0
          in  (\x -> (2013 `safeDiv` z)) (foo z)
\end{code}

<br>

In Haskell, program *skips* `(foo z)` & hits divide-by-zero!

Problem: Divergence
-------------------

<div class="fragment">
What is denoted by `e :: {v:Int | 0 <= v}` ?
</div>

<br>

<div class="fragment">
`e` evaluates to a `Nat`  
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

Suppose `e :: {v:Int | 0 <= v}`

<br>

**Consider**

`let x = e in body`

With Eager Evaluation 
---------------------

Suppose `e :: {v:Int | 0 <= v}`

<br>

**Consider**

`let x = e in body`

<br>

<div class="fragment">
**Can** assume `x` is a `Nat` when checking `body`
</div>

But With Lazy Evaluation 
------------------------

Suppose `e :: {v:Int | 0 <= v}`

<br>

**Consider**

`let x = e in body`

<br>

<div class="fragment">
**Cannot** assume `x` is a `Nat` when checking e!
</div>

Oops. Now what?
---------------

**Solution** 

Only assign *non-trivial* refinements to *non-diverging* terms!

<br>

<div class="fragment">

**Require A Termination Analysis**

(Oh dear...)

</div>

<a href="http://goto.ucsd.edu:8090/index.html#?demo=TellingLies.hs" target="_blank">Demo:</a>Disable `"--no-termination" and see what happens!


Recap
-----

1. **Refinements:** Types + Predicates
2. **Subtyping:** SMT Implication
3. **Measures:** Strengthened Constructors
4. **Abstract Refinements:** Decouple Invariants 
5. **Lazy Evaluation:** Requires Termination
6. <div class="fragment">**Termination:** Via Refinements!</div>

