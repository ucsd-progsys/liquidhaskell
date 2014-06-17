 {#ASD}

Liquid Types For Haskell
------------------------

<br> <br>

**Ranjit Jhala**

University of California, San Diego

<br> <br>

Joint work with:

N. Vazou, E. Seidel, P. Rondon, D. Vytiniotis, S. Peyton-Jones

<div class="hidden">

``` {.sourceCode .literate .haskell}
main = putStrLn "Easter Egg: to force Makefile"
```

</div>

Well-Typed Programs Can Go Wrong
================================

 {#asd}

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
λ> let t = pack "Kanazawa"
λ> takeWord16 5 t
"Kanaz"
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

Liquid Types for Haskell
========================

LiquidHaskell
-------------

<br> <br>

<div class="fragment">

Refine **types** with **predicates**

</div>

<br> <br>

<div class="fragment">

**Expressive** specification & **Automatic** verification

</div>

Automatic
---------

[Liquid Types, PLDI
08](http://goto.ucsd.edu/~rjhala/liquid/liquid_types.pdf)

<br>

-   Abstract Interpretation

-   SMT Solvers

Expressive
----------

<br> <br>

This talk ...

Try Yourself
------------

<br>

**google: ** `"liquidhaskell demo"`

 {#zog}

<br> <br> <br> <br>

[[continue]](01_SimpleRefinements.lhs.slides.html)

Plan
----

1.  <a href="01_SimpleRefinements.lhs.slides.html" target= "_blank">Refinements
2.  <div class="fragment">

    <a href="02_Measures.lhs.slides.html" target= "_blank">Measures</a>

    </div>

3.  <div class="fragment">

    <a href="03_HigherOrderFunctions.lhs.slides.html" target= "_blank">Higher-Order
    Functions</a>

    </div>

4.  <div class="fragment">

    <a href="04_AbstractRefinements.lhs.slides.html" target= "_blank">Abstract
    Refinements:</a>
    <a href="06_Inductive.lhs.slides.html" target="_blank">Code</a>,
    <a href="08_Recursive.lhs.slides.html" target= "_blank">Data</a>,<a href="07_Array.lhs.slides.html" target= "_blank">...</a>,<a href="05_Composition.lhs.slides.html" target= "_blank">...</a>

    </div>

5.  <div class="fragment">

    <a href="09_Laziness.lhs.slides.html" target="_blank">Lazy
    Evaluation</a>

    </div>

6.  <div class="fragment">

    <a href="10_Termination.lhs.slides.html" target="_blank">Termination</a>

    </div>

7.  <div class="fragment">

    <a href="11_Evaluation.lhs.slides.html" target="_blank">Evaluation</a>

    </div>


