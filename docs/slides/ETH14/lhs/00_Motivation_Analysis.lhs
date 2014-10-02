 {#asds}
========

Goal
----

<div class="hidden">

\begin{code}
main = putStrLn "Easter Egg: to force Makefile"
\end{code}

</div>


<br>
<br>


Analysis & Verification of Program Properties


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

Automatic but **not** Expressive

<br>

+ Rich Data Types ?

+ Higher-order functions ?

+ Polymorphism ?


Liquid Types
------------

<br>

Generalize Floyd-Hoare Logic with Types

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

Liquid Types
------------

<br>
<br>

[[continue]](01_SimpleRefinements.lhs.slides.html)


Plan 
----

+ <a href="01_SimpleRefinements.lhs.slides.html" target="_blank">Refinements</a>
+ <div class="fragment"><a href="02_Measures.lhs.slides.html" target= "_blank">Measures</a></div>
+ <div class="fragment"><a href="03_HigherOrderFunctions.lhs.slides.html" target= "_blank">Higher-Order Functions</a></div>
+ <div class="fragment"><a href="04_AbstractRefinements.lhs.slides.html" target= "_blank">Abstract Refinements:</a> <a href="06_Inductive.lhs.slides.html" target="_blank">Code</a>, <a href="08_Recursive.lhs.slides.html" target= "_blank">Data</a>,<a href="07_Array.lhs.slides.html" target= "_blank">...</a>,<a href="05_Composition.lhs.slides.html" target= "_blank">...</a></div>
+ <div class="fragment"><a href="09_Laziness.lhs.slides.html" target="_blank">Lazy Evaluation</a></div>
+ <div class="fragment"><a href="10_Termination.lhs.slides.html" target="_blank">Termination</a></div>
+ <div class="fragment"><a href="11_Evaluation.lhs.slides.html" target="_blank">Evaluation</a></div>
+ <div class="fragment"><a href="12_Conclusion.lhs.slides.html" target="_blank">Conclusion</a></div>

