 {#ASD}
-------

Liquid Types For Haskell
------------------------


<br>
<br>
<br>

**Ranjit Jhala**

University of California, San Diego

<br>
<br>
<br>


Joint work with: 

N. Vazou, E. Seidel, P. Rondon, D. Vytiniotis, S. Peyton-Jones


<div class="hidden">

\begin{code}
main = putStrLn "Easter Egg"
\end{code}

</div>


Well-Typed Programs *Can* Go Wrong
==================================

 {#asd}
-------

Division By Zero
----------------

<div class="fragment"> 
\begin{code} <div/> 
λ> let average xs = sum xs `div` length xs

λ> average [1,2,3]
2
\end{code}
</div>

<div class="fragment"> 

\begin{code} <br> 
λ> average []
*** Exception: divide by zero
\end{code}

</div>

Missing Keys
------------

<div class="fragment"> 
\begin{code} <div/> 
λ> :m +Data.Map 
λ> let m = fromList [ ("haskell", "lazy")
                    , ("ocaml"  , "eager")]

λ> m ! "haskell"
"lazy"
\end{code}
</div>

<div class="fragment"> 
\begin{code} <br> 
λ> m ! "javascript"
"*** Exception: key is not in the map
\end{code}
</div>

Segmentation Faults
-------------------

<div class="fragment"> 
\begin{code} <div/> 
λ> :m +Data.Vector 
λ> let v = fromList ["haskell", "ocaml"]
λ> unsafeIndex v 0
"haskell"
\end{code}
</div>

<div class="fragment"> 
\begin{code} <br> 
λ> V.unsafeIndex v 3


'ghci' terminated by signal SIGSEGV ...
\end{code}
</div>


"HeartBleeds"
-------------

\begin{code} <div/>
λ> :m + Data.Text Data.Text.Unsafe 
λ> let t = pack "kamakura"
λ> takeWord16 5 t
"kamak"
\end{code}

<br>

<div class="fragment"> 
Memory overflows **leaking secrets**...

<br>

\begin{code} <div/>
λ> takeWord16 20 t
"kamakura\1912\3148\SOH\NUL\15928\2486\SOH\NUL"
\end{code}
</div>

Goal
----

Extend Hindley-Milner To Prevent More Errors

Refinement Types for Haskell
============================

LiquidHaskell
-------------

<div class="fragment">Refine *types* with *predicates*</div>

<br>

<div class="fragment">*Expressive* specification & *Automatic* verification</div>



Automatic
---------

[Liquid Types, PLDI 08](http://goto.ucsd.edu/~rjhala/liquid/liquid_types.pdf)

<br>

+ Abstract Interpretation 

+ SMT Solvers 

Expressive
----------

+ This talk ...

Try Yourself
------------

<br>

**google: ** `"liquidhaskell demo"` 

 {#plan} 
--------

1. <div class="fragment"><a href="01_SimpleRefinements.lhs.slides.html" target= "_blank">Refinements</a></div>
2. <div class="fragment"><a href="02_Measures.lhs.slides.html" target= "_blank">Measures</a></div>
3. <div class="fragment"><a href="03_HigherOrderFunctions.lhs.slides.html" target= "_blank">Higher-Order Functions</a></div>
4. <div class="fragment"><a href="04_AbstractRefinements.lhs.slides.html" target= "_blank">Abstract Refinements:</a> <a href="06_Inductive.lhs.slides.html" target="_blank">Code</a>, <a href="08_Recursive.lhs.slides.html" target= "_blank">Data</a>,<a href="07_Array.lhs.slides.html" target= "_blank">...</a>,<a href="05_Composition.lhs.slides.html" target= "_blank">...</a></div>
5. <div class="fragment"><a href="09_Laziness.lhs.slides.html" target="_blank">Lazy Evaluation</a></div>
6. <div class="fragment"><a href="10_Termination.lhs.slides.html" target="_blank">Termination</a></div>
 
Evaluation
==========

LiquidHaskell Is For Real
-------------------------

<br>

Substantial code bases, tricky properties.

<br>

<div class="fragment">Inference is crucial.</div>

Numbers
-------

<div align="center">

**Library**                     **LOC**
---------------------------   ---------
`Data.List`                         814
`Data.Set.Splay`                    149
`Data.Vector.Algorithms`           1219
`Data.Map.Base`                    1396
`Data.Text`                        3125
`Data.Bytestring`                  3501 
**Total**                     **10224**
---------------------------   ---------

</div>

Termination
-----------

Proving termination is *easy*, in practice.

<br>

- <div class="fragment">`503` recursive functions</div>
- <div class="fragment">`67%` automatically proved</div>
- <div class="fragment">`30%` need *witnesses* `/[...]`</div>
- <div class="fragment">`1`   termination hint per `100` lines of code</div>
- <div class="fragment">`18`  *not proven* to terminate</div>
- <div class="fragment">`12`  *do not* terminate (e.g. top-level `IO` loops)</div>
- <div class="fragment">`6`   *probably* terminate, but *we* can't tell why.</div>


Future Work
-----------

- <div class="fragment">Speed</div>

- <div class="fragment">Case Studies</div>

- <div class="fragment">**Error Messages**</div>

Thank You!
----------

<br>


`cabal install liquidhaskell`

<br>

`https://github.com/ucsd-progsys/liquidhaskell`

<br>
