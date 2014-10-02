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

(Automatically) Proving Properties of Programs 

Algorithmic Verification
========================

A Classic Example 
-----------------

<img src="../img/minindex-classic.png" height=300px>

**Verify:** indices `i`, `min` are *within bounds* of `arr`

Easy, use **Logic** + **Analysis**

Logic 
-----

<img src="../img/minindex-invariant.png" height=300px>

-------------------   ----------------------------------------------------
**Specification**     *Predicates* (invariants, pre-/post-conditions)
**Proof**             *Verification Conditions* checked by SMT solver
-------------------   ----------------------------------------------------

<div class="fragment">
[ESC, Spec#, Dafny, VCC, ...]
</div>

<div class="fragment">
No invariants? **Inference** via Analysis...
</div>

Analysis 
--------

+ Invariants are *fixpoints* of reachable states

+ Compute via *Dataflow Analysis* or *Abstract Interpretation*

<div class="fragment">
[ABCD, ASTREE, BLAST, CLOUSOT, SATURN, SLAM, ...]
</div>


Logic + Analysis 
----------------

-------------------   ----------------------------------------------------
**Specification**     *Predicates* (invariants, pre-/post-conditions)
**Proof**             *Verification Conditions* checked by SMT solver
**Inference**         *Fixpoint* over abstract domain
-------------------   ----------------------------------------------------

<div class="fragment">
But ... limited to "classical" programs!
</div>


"Classical" vs. "Modern" Programs
---------------------------------

**"Classical" Programs**

+ <div class="fragment">Assignment + Branches + Sequencing + Loops </div>
+ <div class="fragment">Procedures + Recursion</div>
+ <div class="fragment">(Recent) Objects + Classes</div>

**"Modern" Programs**

+ <div class="fragment">Unbounded Containers  (eg. Arrays, Lists, HashMaps)</div>
+ <div class="fragment">Polymorphism          (eg. Generics,...)</div>
+ <div class="fragment">Callbacks/HOFs        (eg. map, reduce, filter,...)<div>


A "Modern" Example 
------------------

<img src="../img/minindex-modern.png" height=300px>

Verify indices `i`, `min` are *within bounds* of `arr`

<div class="fragment">Many vexing problems for Logic + Analysis</div>

+ <div class="fragment">How to **assert**      facts about *unbounded* contents of `arr`?</div>
+ <div class="fragment">How to **summarize**   behavior of `reduce` independent of `callback`?</div>
+ <div class="fragment">How to **instantiate** summary at different *contexts* ?</div>


This Talk: Liquid Types
-----------------------


<br>
Use **Types** to lift **Logic + Analysis** to Modern Programs 

<div class="fragment"> 
-------------------   ------------------------------------------------
**Properties:**       Predicates *+ Types*
**Proofs:**           Verification Conditions *+ Subtyping* 
**Inference:**        Abstract Interpretation *+ Hindley-Milner*
-------------------   ------------------------------------------------
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
+ <div class="fragment"><a href="04_AbstractRefinements.lhs.slides.html" target= "_blank">Abstract Refinements:</a><a href="08_Recursive.lhs.slides.html" target= "_blank">Data</a>,<a href="07_Array.lhs.slides.html" target= "_blank">Data</a>,<a href="06_Inductive.lhs.slides.html" target="_blank">Code</a>.</div>
+ <div class="fragment"><a href="11_Evaluation.lhs.slides.html" target="_blank">Evaluation</a></div>
+ <div class="fragment"><a href="12_Conclusion.lhs.slides.html" target="_blank">Conclusion</a></div>

