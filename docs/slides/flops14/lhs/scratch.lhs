<!--


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
https://github.com/ucsd-progsys/liquidhaskell`


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
