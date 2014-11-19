 {#ASda}
========

Evaluation
----------

<div class="hidden">

\begin{code}
main = putStrLn "Easter Egg: to force Makefile"
\end{code}

</div>


Evaluation
==========

LiquidHaskell 
-------------

<br>

**Diverse Code Bases**

<br>

10KLoc

<br>

56 Modules

LiquidHaskell 
-------------

<br>

**Complex Properties**

<br>

Memory Safety


Functional Correctness*


Termination

<br>

<div class="fragment">
**Inference is Crucial**
</div>

Benchmarks
----------

<div align="center">

**Library**                     
---------------------------   ---------
`XMonad.StackSet`                      
`Data.List`                         
`Data.Set.Splay`                    
`Data.Vector.Algorithms`           
`HsColour`                        
`Data.Map.Base`                
`Data.Text`                        
`Data.Bytestring`                  
---------------------------   ---------

</div>


Benchmarks 
----------

<div align="center">

**Library**                     **LOC**
---------------------------   ---------
`XMonad.StackSet`                   256 
`Data.List`                         814
`Data.Set.Splay`                    149
`Data.Vector.Algorithms`           1219
`HsColour`                         1047
`Data.Map.Base`                    1396
`Data.Text`                        3128
`Data.Bytestring`                  3505
**Total**                     **11512**
---------------------------   ---------

</div>

Benchmarks
----------

<div align="center">

**Library**                     **LOC**     **Specs**    
---------------------------   ---------   -----------    
`XMonad.StackSet`                   256            74    
`Data.List`                         814            46    
`Data.Set.Splay`                    149            27    
`Data.Vector.Algorithms`           1219            76    
`HsColour`                         1047            19    
`Data.Map.Base`                    1396           125    
`Data.Text`                        3128           305    
`Data.Bytestring`                  3505           307    
**Total**                     **11512**       **977**    
---------------------------   ---------   -----------    

</div>


Code v. Specs 
-------------

<img src="../img/code-spec-indiv.png" height=400px>


Code v. Specs 
-------------

<br>

<img src="../img/code-spec-total.png" height=100px>
 
**About 8.5%**

*Very* coarse measure...

Running Time
------------

<div align="center">

**Library**                     **LOC**     **Specs**      **Time**
---------------------------   ---------   -----------    ----------
`XMonad.StackSet`                   256            74          27s
`Data.List`                         814            46          26s
`Data.Set.Splay`                    149            27          27s
`Data.Vector.Algorithms`           1219            76          89s 
`HsColour`                         1047            19         196s
`Data.Map.Base`                    1396           125         174s
`Data.Text`                        3128           305         499s
`Data.Bytestring`                  3505           307         294s
**Total**                     **11512**       **977**    **1336s**
---------------------------   ---------   -----------    ----------

</div>



 {#comments}
============

Types as Comments
-----------------

<br>

**Types are Machine Checked Comments**

<br>

+ Express same *requirements*

+ But *connected to* code

<br>

<div class="fragment">
**Always in sync as code changes**
</div>

Liquid Types as Machine Checked Comments
========================================

Example: Data.Map
-----------------

<br>

**Requirement**

<br>

`Map a b` is a *binary search* ordered tree

Example: Data.Map
-----------------

**Comment**

\begin{spec}
-- @join@ assumes that all values in [l] < [k]
-- and all values in [r] > [k], and
-- that [l] and [r] are valid trees.
\end{spec}

<br>

<div class="fragment">

**Type**

\begin{spec}
join :: k:a -> b
     -> l:Map {v:a | v < k} b
     -> r:Map {v:a | v > k} b
     -> Map a b 
\end{spec}

</div>

Example: Data.ByteString
------------------------

<br>

**Requirement**

<br>

Fast, low-level indices into a `ByteString` must be in bounds.


Example: Data.ByteString
------------------------

**Comment**

\begin{spec}
-- Unsafe 'ByteString' index (subscript) ...
-- omits the bounds check, which means there
-- is an obligation to ensure the bounds are
-- checked in some other way.
\end{spec}

<br>

<div class="fragment">

**Type**

\begin{spec}
unsafeIndex :: b:ByteString
            -> {v:Nat | v < bLength b}
            -> Word8 
\end{spec}

</div>

Example: Data.ByteString
------------------------

<br>

**Requirement**

<br>

Fast *truncation* requires valid size.


Example: Data.ByteString
------------------------

**Comment**

\begin{spec}
-- omits the checks on @n@ so there is
-- an obligation to provide a proof
-- that @0 <= n <= 'length' xs@             
\end{spec}

<br>

<div class="fragment">
**Type**

\begin{spec}
unsafeTake :: n:Nat
           -> {v:ByteString | n <= bLength v}
           -> {v:ByteString | n = bLength v} 
\end{spec}

</div>

 {#cont}
=========


Continue
--------

<br>
<br>
<br>

[[continue...]](12_Conclusion.lhs.slides.html)

 {#recap}
=========


Recap
-----

1. Refinements: Types + Predicates
2. Subtyping: SMT Implication
3. Measures: Strengthened Constructors
4. Abstract: Refinements over functions and data
5. **Evaluation**
6. <div class="fragment"><a href="12_Conclusion.lhs.slides.html" target="_blank">Conclusion</a></div>

<br>
<br>

