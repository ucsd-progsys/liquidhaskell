Refinement Types For Haskell
============================

 {#berg} 
--------

<br>

+ Niki Vazou
+ Eric Seidel
+ *Ranjit Jhala*

<br>

**UC San Diego**

<div class="hidden">

\begin{code}
main = putStrLn "Easter Egg"
\end{code}

</div>

Install
-------

<br>

`cabal install liquidhaskell`

<br>

<div class="fragment"> 

  Requires an SMTLIB2 binary 
  
  <br>

  + `http://z3.codeplex.com`
  + `http://cvc4.cs.nyu.edu`
  + `http://mathsat.fbk.eu`

</div>

Try Online
----------

<br>

`http://goto.ucsd.edu/liquid/haskell/demo`

Follow Slides
-------------

<br>

`goto.ucsd.edu/~rjhala/liquid/haskell/plpv/lhs/`


 {#plan} 
--------

1. <div class="fragment"><a href="01_SimpleRefinements.lhs.slides.html" target= "_blank">Refinements</a></div>
2. <div class="fragment"><a href="02_Measures.lhs.slides.html" target= "_blank">Measures</a></div>
3. <div class="fragment"><a href="03_HigherOrderFunctions.lhs.slides.html" target= "_blank">Higher-Order Functions</a></div>
4. <div class="fragment"><a href="04_AbstractRefinements.lhs.slides.html" target= "_blank">Abstract Refinements</a></div>
    - <div class="fragment"><a href="05_Composition.lhs.slides.html" target="_blank">Dependency</a><a href="06_Inductive.lhs.slides.html" target= "_blank">, Induction</a> <a href="07_Array.lhs.slides.html" target= "_blank">, Indexing</a> <a href="08_Recursive.lhs.slides.html" target= "_blank">, Recursion</a></div>
5. <div class="fragment"><a href="09_Laziness.lhs.slides.html" target="_blank">Lazy Evaluation</a></div>
6. <div class="fragment"><a href="10_Termination.lhs.slides.html" target="_blank">Termination</a></div>

<!--

[Higher Order Functions](03_HigherOrderFunctions.lhs.slides.html)
   </div>
4. <div class="fragment">
      [Abstract Refinements](04_AbstractRefinements.lhs.slides.html)
   </div>
    - <div class="fragment">[Dependency](05_Composition.lhs.slides.html), 
                            [Induction](06_Inductive.lhs.slides.html), 
                            [Indexing](07_Array.lhs.slides.html), 
                            [Recursion](08_Recursive.lhs.slides.html)
      </div>
5. <div class="fragment">
    [Lazy Evaluation](09_Laziness.lhs.slides.html)
   </div>
6. <div class="fragment">
     [Termination](10_Termination.lhs.slides.html)
   </div>

-->

Evaluation
==========

LiquidHaskell Is For Real
-------------------------

<br>

Substantial code bases, tricky properties.

<br>

<div class="fragment">Inference, FTW.</div>

Numbers
-------

<div align="center">

**Library**                      LOC
---------------------------   ------
`GHC.List`                       310
`Data.List`                      504
`Data.Set.Splay`                 149
`Data.Vector.Algorithms`        1219
`Data.Map.Base`                 1396
`Data.Text`                     3125
`Data.Bytestring`               3501 
---------------------------   ------

</div>

Evaluation: Termination
-----------------------

How bad is *termination* requirement anyway?

- <div class="fragment">`520` recursive functions</div>
- <div class="fragment">`67%` automatically proved</div>
- <div class="fragment">`30%` need *witnesses* `/[...]`</div>
- <div class="fragment">`18`  *not proven terminating*</div>
- <div class="fragment">`12`  don't actually terminate (top-level `IO`)</div>
- <div class="fragment">`6`   *probably* terminate, but *we* can't tell why.</div>


Future Work
-----------

- Error Messages

- Speed

- Case Studies

Thank You!
----------

`cabal install liquidhaskell`

