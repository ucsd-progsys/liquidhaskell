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
                    , ("pyret"  , "eager")]

λ> m ! "haskell"
"lazy"
\end{spec}
</div>

<br>

<div class="fragment"> 
\begin{spec}
λ> m ! "racket"
"*** Exception: key is not in the map
\end{spec}
</div>

Segmentation Faults
-------------------

<div class="fragment"> 
\begin{spec}
λ> :m +Data.Vector 
λ> let v = fromList ["haskell", "pyret"]
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
λ> let t = pack "Shriram"
λ> takeWord16 5 t
"Shrir"
\end{spec}

<br>

<div class="fragment"> 
Memory overflows **leaking secrets**...

<br>

\begin{spec}
λ> takeWord16 20 t
"Shriram\1912\3148\SOH\NUL\15928\2486\SOH\NUL"
\end{spec}
</div>

Goal
----

Extend Type System

<br>

+ To prevent *wider class* of errors

+ To enforce *program specific* properties 


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

<div class="fragment"> 
<br>

+ **Properties:**  Types + Predicates

+ **Proofs:**      Subtyping + Verification Conditions

+ **Inference:**   Hindley-Milner + Abstract Interpretation

</div>

<div class="fragment"> 
  <br>
  Towards reconciling Automation and Expressiveness
</div>

END CUT -->

Refinement Types
----------------

<br>
<br>

[[continue]](01_SimpleRefinements.lhs.slides.html)



