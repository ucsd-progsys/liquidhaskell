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

Substantial code bases.

<br>

Complex properties.

<br>

<div class="fragment">Inference is crucial.</div>


Numbers
-------

<div align="center">

**Library**                     **LOC**     **Time**
---------------------------   ---------   ----------
`Data.List`                         814          52s
`Data.Set.Splay`                    149          26s
`Data.Vector.Algorithms`           1219         196s 
`Data.Map.Base`                    1396         247s
`Data.Text`                        3125         809s
`Data.Bytestring`                  3501         549s
**Total**                     **10224**    **1880s**
---------------------------   ---------   ----------

</div>



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
