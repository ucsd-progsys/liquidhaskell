 {#asds}
========

Algorithmic Verification 
------------------------


<div class="hidden">

\begin{code}
main = putStrLn "Easter Egg: to force Makefile"
\end{code}

</div>

<br>
<br>

**Goal**

<br>

Automatically Proving Properties of Programs 

Algorithmic Verification
========================

A Classic Example 
-----------------

<img src="../img/minindex-classic.png" height=300px>

**Verify:** indices `i`, `min` are *within bounds* of `arr`

A Classic Example 
-----------------

<img src="../img/minindex-classic.png" height=300px>

Easy, use Program **Logic** + **Analysis**

Program Logic 
-------------

<img src="../img/minindex-invariant.png" height=300px>

-------------------   ----------------------------------------------------
**Specification**     *Predicates* eg. invariants, pre-/post-conditions
**Verification**      *Conditions* checked by SMT solver
-------------------   ----------------------------------------------------

Program Logic 
-------------

<br>

-------------------   ----------------------------------------------------
**Specification**     *Predicates* eg. invariants, pre-/post-conditions
**Verification**      *Conditions* checked by SMT solver
-------------------   ----------------------------------------------------

<br>

No invariants? **Inference** via Analysis...

Program Analysis 
----------------

<br>

**Invariants are Fixpoints of Reachable States**

<br>

Computable via *Dataflow Analysis* or *Abstract Interpretation*

<br>

Logic + Analysis 
----------------

<br>

-------------------   ----------------------------------------------------
**Specification**     *Predicates*, eg. invariants, pre-/post-conditions
**Verification**      *Conditions* checked by SMT solver
**Inference**         *Fixpoint* over abstract domain
-------------------   ----------------------------------------------------

<br>

<div class="fragment">
But ... limited to "classical" programs!
</div>


"Classical" vs. "Modern" Programs
=================================


 {#classicalvmodern}
--------------------


"Classical" Programs
--------------------

<br>

<div class="fragment">
**Imperative**

Assignments, Branches, Loops
</div>

<br>

<div class="fragment">
**First-Order Functions**

Recursion 
</div>

<br>

<div class="fragment">
**Objects**

Classes, Inheritance*
</div>


"Modern" Programs
-----------------


<div class="fragment">
**Containers**

Arrays, Lists, HashMaps,...

</div>

<br>

<div class="fragment">
**Polymorphism**

Generics, Typeclasses...
</div>

<br>

<div class="fragment">
**Higher Order Functions**

Callbacks, map, reduce, filter,...
</div>


A "Modern" Example 
------------------

<img src="../img/minindex-modern.png" height=300px>

Verify indices `i`, `min` are *within bounds* of `arr`

A "Modern" Example 
------------------

<img src="../img/minindex-modern.png" height=300px>

Pose vexing challenges for Logic + Analysis

Logic + Analysis Challenges
----------------------------

<img src="../img/minindex-modern.png" height=250px>

+ How to analyze **unbounded** contents of `arr`?
+ <div class="fragment">How to **summarize** `reduce` independent of `callback`?</div>
+ <div class="fragment">How to precisely reuse summary at each **context** ?</div>


 {#motiv}
=========

Logic + Analysis + *Types*
--------------------------


Logic + Analysis + *Types*
==========================


Refinement Types
----------------

<br>

Use **Types** to lift **Logic + Analysis** to Modern Programs 

<br>

<div class="fragment">

-----   ----   ---   ----   -------------------   -------------------------------------------
                            **Specification**     *Types* + Predicates 
                            **Verification**      *Subtyping* + Verification Conditions
                            **Inference**         *Type Inference* + Abstract Interpretation
-----   ----   ---   ----   -------------------   -------------------------------------------

<br>
<br>

[[continue]](01_SimpleRefinements.lhs.slides.html)

</div>

Refinement Types
----------------



<br>
<br>

Plan 
----

+ <a href="01_SimpleRefinements.lhs.slides.html" target="_blank">Refinements</a>
+ <div class="fragment"><a href="02_Measures.lhs.slides.html" target= "_blank">Measures</a></div>
+ <div class="fragment"><a href="03_HigherOrderFunctions.lhs.slides.html" target= "_blank">Higher-Order Functions</a></div>
+ <div class="fragment"><a href="04_AbstractRefinements.lhs.slides.html" target= "_blank">Abstract Refinements:</a><a href="06_Inductive.lhs.slides.html" target="_blank">Code</a>,<a href="07_Array.lhs.slides.html" target= "_blank">Data</a></div>
+ <div class="fragment"><a href="11_Evaluation.lhs.slides.html" target="_blank">Evaluation</a></div>
+ <div class="fragment"><a href="12_Conclusion.lhs.slides.html" target="_blank">Conclusion</a></div>

<br>
<br>



<div class="fragment">[[continue...]](01_SimpleRefinements.lhs.slides.html)</div>
