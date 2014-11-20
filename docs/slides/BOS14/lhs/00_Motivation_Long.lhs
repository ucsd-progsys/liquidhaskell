
 {#intro}
=========

 {#firstbug0}
-------------

<img src="../img/firstbug-crop.jpg" height=400px>

The First *Bug* 
---------------

<img src="../img/firstbug-crop2.jpg" height=300px>

**Page from Harvard Mark II log**

A dead moth removed from the device

<!-- BEGIN CUT

Morris Worm (1988)
------------------

<img src="../img/RobertMorris.png" height=300px>

+ **Buffer overflow** in `fingerd`

+ "Breaks internet" for several days

+ Harmless internet probe gone berserk

END CUT -->

Slammer Worm (2003)
-------------------

<img src="../img/sapphire.gif" height=300px>

**Buffer Overflow**

Affected 90% of vulnerable machines in 10 mins

Northeast Blackout (2003)
-------------------------

<img src="../img/blackout.gif" height=300px>

**Race Condition**

Cut power for 55 million, trigger: lines hitting foliage

HeartBleed (2014)
-----------------

<img src="../img/heartbleed.png" height=300px>

**Buffer Overflow**

Compromises secret keys, passwords ...


Goto Fail (2014)
----------------

<img src="../img/gotofail.png" height=300px>

**Typo (?!)**

Bypass critical check, compromise cryptography

A Possible Solution
===================

 Modern Languages
-----------------

<div class="fragment">

<img src="../img/george-orwell.jpg" height=250px>

</div>

<div class="fragment">

<img src="../img/thoughtcrime.png" height=100px>

</div>

Modern Languages
----------------

<br>

F#

Rust

Scala

Ocaml

**Haskell**


Modern Languages
----------------

<br>

Static Typing

<br>

First-class Functions

<br>

Immutability by Default


<br>

<div class="fragment">

Make **good** designs **easy** and **bad** designs **hard**

</div>


Modern Languages? 
-------------------

<br>

Not so fast ...

<br>

<div class="fragment">

Well-typed programs **can go wrong!**

</div>


Well-Typed Programs Can Go Wrong
================================

 {#asd}
-------

<div class="hidden">

\begin{code}
main = putStrLn "Easter Egg: to force Makefile"
\end{code}

</div>


Division By Zero
----------------




<div class="fragment"> 
\begin{spec}
λ> let average xs = sum xs `div` length xs

λ> average [1,2,3]
2
\end{spec}
</div>

<br>

<div class="fragment"> 
\begin{spec}  
λ> average []
*** Exception: divide by zero
\end{spec}

</div>

Missing Keys
------------

<div class="fragment"> 
\begin{spec}  
λ> :m +Data.Map 
λ> let m = fromList [ ("haskell", "lazy")
                    , ("racket" , "eager")]

λ> m ! "haskell"
"lazy"
\end{spec}
</div>

<br>

<div class="fragment"> 
\begin{spec}
λ> m ! "javascript"
"*** Exception: key is not in the map
\end{spec}
</div>

Segmentation Faults
-------------------

<div class="fragment"> 
\begin{spec}
λ> :m +Data.Vector 
λ> let v = fromList ["haskell", "racket"]
λ> unsafeIndex v 0
"haskell"
\end{spec}
</div>

<div class="fragment"> 
<br>
\begin{spec} 
λ> V.unsafeIndex v 3


'ghci' terminated by signal SIGSEGV ...
\end{spec}
</div>


"HeartBleeds"
-------------

\begin{spec}
λ> :m + Data.Text Data.Text.Unsafe 
λ> let t = pack "Norman"
λ> takeWord16 4 t
"Norm"
\end{spec}

<br>

<div class="fragment"> 
Memory overflows **leaking secrets**...

<br>

\begin{spec}
λ> takeWord16 20 t
"Norman\1912\3148\SOH\NUL\15928\2486\SOH\NUL"
\end{spec}
</div>

Goal
----

<br>

Extend Type System

<br>

+ To prevent *wider class* of errors

+ To enforce *program specific* properties 

<br>

<div class="fragment">

**Without sacrificing automation** 

</div>

Algorithmic Verification
========================

Tension
-------

<img src="../img/tension0.png" height=300px>

Automation vs. Expressiveness

Tension
-------

<img src="../img/tension1.png" height=300px>

Extremes: Hindley-Milner vs. CoC

Tension
-------

<img src="../img/tension2.png" height=300px>

Trading off Automation for Expressiveness

Tension
-------

<img src="../img/tension3.png" height=300px>

**Goal:** Find a sweet spot?

<!-- BEGIN CUT

Program Logics
--------------

<br>

**Floyd-Hoare** (ESC, Dafny, SLAM/BLAST,...)

<br>

+ **Properties:**   Assertions & Pre- and Post-conditions

+ **Proofs:**       Verification Conditions proved by SMT

+ **Inference:**    Abstract Interpretation

<br>

<div class="fragment"> Automatic but **not** Expressive </div>

END CUT -->

Program Logics
--------------

<br>

**Floyd-Hoare** (ESC, Dafny, SLAM/BLAST,...)


<br>

Automatic but **not** Expressive

<br>

+ Rich Data Types ?

+ Higher-order functions ?

+ Polymorphism ?

Refinement Types
----------------

<br>

Generalize *Program Logics* with *Types*

<br>

+ **Properties:**  Types + Predicates

+ **Proofs:**      Subtyping + SMT Solvers

<!-- BEGIN CUT
+ **Inference:**   Hindley-Milner + Abstract Interpretation
  -->

<div class="fragment"> 
  <br>
  Towards reconciling Automation and Expressiveness
</div>

<br>

<div class="fragment"> 
[[continue]](01_SimpleRefinements.lhs.slides.html)
</div>

