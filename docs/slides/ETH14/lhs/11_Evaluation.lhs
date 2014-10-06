 {#ASda}
========

Evaluation
----------



Evaluation
==========

LiquidHaskell Is For Real
-------------------------

<div class="hidden">

\begin{code}
main = putStrLn "Easter Egg: to force Makefile"
\end{code}

</div>

<br>

**Substantial Code Bases**

10KLoc, 50+ Modules

<br>

**Complex Properties**

Memory Safety, Functional Correctness*, Termination

<br>

<div class="fragment">
**Inference is Crucial**
</div>


Numbers
-------

<div align="center">

**Library**                     **LOC**
---------------------------   ---------
`Data.List`                         814
`Data.Set.Splay`                    149
`Data.Vector.Algorithms`           1219
`HsColour`                         1047
`Data.Map.Base`                    1396
`Data.Text`                        3125
`Data.Bytestring`                  3501
**Total**                     **11251**
---------------------------   ---------

</div>

Numbers
-------

<div align="center">

**Library**                     **LOC**     **Time**
---------------------------   ---------   ----------
`Data.List`                         814          26s
`Data.Set.Splay`                    149          27s
`Data.Vector.Algorithms`           1219          89s 
`HsColour`                         1047         196s
`Data.Map.Base`                    1396         174s
`Data.Text`                        3125         499s
`Data.Bytestring`                  3501         294s
**Total**                     **11251**    **1305s**
---------------------------   ---------   ----------

</div>

Recap
-----

1. Refinements: Types + Predicates
2. Subtyping: SMT Implication
3. Measures: Strengthened Constructors
4. Abstract: Refinements over functions and data
5. **Evaluation**
5. <div class="fragment"><a href="12_Conclusion.lhs.slides.html" target="_blank">Conclusion</a></div>

<br>
<br>

<div class="fragment">[[continue...]](12_Conclusion.lhs.slides.html)</div>
