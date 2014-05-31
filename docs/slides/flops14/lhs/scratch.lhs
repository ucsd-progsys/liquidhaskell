<!--

Missing Keys
------------

\begin{code} _ 
λ> let m = Map.fromList [("haskell", "lazy"), ("ocaml", "eager")]

λ> m ! "haskell"
"lazy"
\end{code}

<div class="fragment"> 
\begin{code} _ 
λ> m ! "javascript"
"*** Exception: Map.!: given key is not an element in the map
\end{code}
</div>

Segmentation Faults
-------------------

\begin{code} _ 
λ> import qualified Data.Vector as V 

λ> let v = V.fromList ["haskell", "ocaml"]

λ> V.unsafeIndex v 0
"haskell"

λ>  V.unsafeIndex v 1
"ocaml"
\end{code}

<div class="fragment"> 
\begin{code} _ 
λ> V.unsafeIndex v 3

'ghci' terminated by signal SIGSEGV (Address boundary error)
\end{code}
</div>


"HeartBleeds"
-------------

\begin{code} _
λ> import qualified Data.Text as T
λ> import qualified Data.Text.Unsafe as U
λ> let t = T.pack "kamakura"
λ>  U.takeWord16 5 t
"kamak"
\end{code}

<div class="fragment"> 
\begin{code} _
λ> U.takeWord16  20 t
"kamakura\1912\3148\SOH\NUL\15928\2486\SOH\NUL\14834\3444\SOH\NUL"
\end{code}
</div>


Goal: Hindley-Milner++ 
======================

 {#zxc}
-------

Extend HM to prevent *going wrong*

+ Automatic Verification

+ Expressive Specification



LiquidHaskell: Refinement Types for Haskell
-------------------------------------------

Automatic

+ SMT & Abstract Interpretation 

+ [Liquid Types, PLDI 08](http://goto.ucsd.edu/~rjhala/liquid/liquid_types.pdf)

Expressive

+ This talk  


LiquidHaskell
=============

Install
-------

<br>

`cabal install liquidhaskell`

<br>


<!-- 
<div class="fragment"> 

  Requires an SMTLIB2 binary 
  
  <br>

  + `http://z3.codeplex.com`
  + `http://cvc4.cs.nyu.edu`
  + `http://mathsat.fbk.eu`

</div>

-->

Try Online
----------

<br>

`http://goto.ucsd.edu/liquid/haskell/demo`


 {#plan} 
--------

1. <div class="fragment"><a href="01_SimpleRefinements.lhs.slides.html" target= "_blank">Refinements</a></div>
2. <div class="fragment"><a href="02_Measures.lhs.slides.html" target= "_blank">Measures</a></div>
3. <div class="fragment"><a href="03_HigherOrderFunctions.lhs.slides.html" target= "_blank">Higher-Order Functions</a></div>
4. <div class="fragment"><a href="04_AbstractRefinements.lhs.slides.html" target= "_blank">Abstract Refinements:</a></div>
      <a href="06_Inductive.lhs.slides.html" target= "_blank">Code</a>,  
      <a href="08_Recursive.lhs.slides.html" target= "_blank">Data</a></div>,
      <a href="05_Composition.lhs.slides.html" target="_blank">...</a>,
      <a href="05_Composition.lhs.slides.html" target="_blank">...</a>
   </div>
5. <div class="fragment"><a href="09_Laziness.lhs.slides.html" target="_blank">Lazy Evaluation</a></div>
6. <div class="fragment"><a href="10_Termination.lhs.slides.html" target="_blank">Termination</a></div>

   <!--
    - <div class="fragment"><a href="05_Composition.lhs.slides.html" target="_blank">Dependency</a>
      <a href="06_Inductive.lhs.slides.html" target= "_blank">, Induction</a> 
      <a href="07_Array.lhs.slides.html" target= "_blank">, Indexing</a> 
      <a href="08_Recursive.lhs.slides.html" target= "_blank">, Recursion</a></div>
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

-->
