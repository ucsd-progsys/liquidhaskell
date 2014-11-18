Termination {#termination}
==========================


<div class="hidden">
\begin{code}
module Termination where

import Prelude hiding (gcd, mod, map)
fib :: Int -> Int
gcd :: Int -> Int -> Int
infixr `C`

data L a = N | C a (L a)

{-@ invariant {v: L a | 0 <= llen v} @-}

mod :: Int -> Int -> Int
mod a b
  | a - b >  b = mod (a - b) b
  | a - b <  b = a - b
  | a - b == b = 0

merge :: Ord a => L a -> L a -> L a
\end{code}
</div>

<!-- BEGIN CUT

Dependent != Refinement
-----------------------

<div class="fragment">**Dependent Types**</div>

+ <div class="fragment">*Arbitrary terms* appear inside types</div> 
+ <div class="fragment">Termination ensures well-defined</div>

<br>

<div class="fragment">**Refinement Types**</div>

+ <div class="fragment">*Restricted refinements* appear in types</div>
+ <div class="fragment">Termination *not* required ...</div> 
+ <div class="fragment">... except, alas, with *lazy* evaluation!</div>

END CUT -->

Refinements & Termination
-------------------------

<div class="fragment">
Fortunately, we can ensure termination **using refinements**
</div>


Main Idea
---------

Recursive calls must be on **smaller** inputs

<br>

+ [Turing](http://classes.soe.ucsc.edu/cmps210/Winter11/Papers/turing-1936.pdf)
+ [Sized Types](http://dl.acm.org/citation.cfm?id=240882)
+ [DML](http://dl.acm.org/citation.cfm?id=609232)
+ [Size Change Principle](http://dl.acm.org/citation.cfm?id=360210)

Recur On *Smaller* `Nat` 
------------------------

<div class="fragment">

**To ensure termination of**

\begin{spec} <div/>
foo   :: Nat -> T
foo x =  body
\end{spec}

</div>

<br>

<div class="fragment">
**Check `body` Under Assumption**

`foo :: {v:Nat | v < x} -> T`

<br>

*i.e.* require recursive calls have `Nat` inputs *smaller than* `x`
</div>



Ex: Recur On *Smaller* `Nat` 
----------------------------

\begin{code}
{-@ fib  :: Nat -> Nat @-}
fib 0    = 1
fib 1    = 1
fib n    = fib (n-1) + fib (n-2)
\end{code}

<br>

<div class="fragment">
Terminates, as both `n-1` and `n-2` are `< n`
</div>

<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=GCD.hs" target="_blank">Demo:</a> &nbsp; What if we drop the `fib 1` equation? 
</div>

Refinements Are Essential!
--------------------------

\begin{code}
{-@ gcd :: a:Nat -> {b:Nat | b < a} -> Int @-}
gcd a 0 = a
gcd a b = gcd b (a `mod` b)
\end{code}

<br>

<div class="fragment">
Need refinements to prove `(a mod b) < b` at *recursive* call!
</div>

<br>

<div class="fragment">
\begin{code}
{-@ mod :: a:Nat 
        -> b:{v:Nat|0 < v && v < a} 
        -> {v:Nat| v < b}           @-}
\end{code}
</div>

Recur On *Smaller* Inputs
-------------------------

<br>

What of input types other than `Nat` ?

<br>

[DEMO](../hs/04_Termination.hs)


Recur On *Smaller* Inputs
-------------------------

What of input types other than `Nat` ?

\begin{spec}<div/>
foo   :: S -> T
foo x = body
\end{spec}

<br>

<div class="fragment">
**Reduce** to `Nat` case...
</div>

<br>

Recur On *Smaller* Inputs
-------------------------

What of input types other than `Nat` ?

\begin{spec}<div/>
foo   :: S -> T
foo x = body
\end{spec}

<br>

Specify a **default measure** `mS :: S -> Int`

<br>

<div class="fragment">
**Check `body` Under Assumption**

`foo :: {v:s | 0 <= mS v < mS x} -> T`
</div>


Ex: Recur on *smaller* `List`
-----------------------------

\begin{code} 
map f N        = N
map f (C x xs) = (f x) `C` (map f xs) 
\end{code}

<br>

Terminates using **default** measure `llen` 

<br>

<div class="fragment">
\begin{code}
{-@ data L [llen] a = N 
                    | C { x::a, xs :: L a} @-}

{-@ measure llen :: L a -> Int
    llen (N)      = 0
    llen (C x xs) = 1 + (llen xs)   @-}
\end{code}
</div>


Recur On *Smaller* Inputs
-------------------------

What of smallness spread across **multiple inputs**?

<br>

\begin{code}
merge xs@(x `C` xs') ys@(y `C` ys')
  | x < y     = x `C` merge xs' ys
  | otherwise = y `C` merge xs ys'
\end{code}

<br>

<div class="fragment">
Neither input decreases, but their **sum** does.
</div>

Recur On *Smaller* Inputs
-------------------------

Neither input decreases, but their **sum** does.

<br>

\begin{code}
{-@ merge :: Ord a => xs:_ -> ys:_ -> _ 
          /  [llen xs + llen ys]     @-}
\end{code}

<br>

<div class="fragment">

Synthesize **ghost** parameter equal to `[...]`

</div>

<br>

<div class="fragment">

... thereby reducing to decreasing **single parameter** case. 

</div>

Important Extensions 
--------------------

<br>

<div class="fragment">**Mutual** recursion</div>

<br>

<div class="fragment">**Lexicographic** ordering</div>

<br>

<div class="fragment">Fit easily into our framework ...</div>

Recap
-----

Main idea: Recursive calls on **smaller** inputs

<br>

<div class="fragment">Use refinements to **check** smaller</div>

<br>

<div class="fragment">Use refinements to **establish** smaller</div>


A Curious Circularity
---------------------

<div class="fragment">Refinements require termination ...</div> 

<br>

<div class="fragment">... Termination requires refinements!</div>

<br>

<div class="fragment"> Meta-theory is tricky, but all ends well.</div>

Termination in Practice
-----------------------

<img src="../img/tension1.png" height=300px>

96% proved *terminating*

61% proved *automatically*

Recap
-----

1. Refinements: Types + Predicates
2. Subtyping: SMT Implication
3. Measures: Strengthened Constructors
4. Abstract: Refinements over functions and data
5. Lazy Evaluation: Requires Termination
6. **Termination:** via Refinements!
7. <div class="fragment">**Evaluation:** How good is this in practice?</div>

<br>
<br>

<div class="fragment">[[continue...]](11_Evaluation.lhs.slides.html)</div>


