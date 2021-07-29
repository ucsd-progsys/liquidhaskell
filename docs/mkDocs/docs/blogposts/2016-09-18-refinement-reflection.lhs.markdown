---
layout: post
title: Haskell as a Theorem Prover
date: 2016-09-18
comments: true
author: Niki Vazou
published: true
tags: reflection
demo: RefinementReflection.hs
---

We've taught LiquidHaskell a new trick that we call ``Refinement Reflection''
which lets us turn Haskell into a theorem prover capable of proving arbitrary
properties of code. The key idea is to **reflect** the code of the function into
its **output type**, which lets us then reason about the function at the
(refinement) type level. Lets see how to use refinement types to express a
theorem, for example that fibonacci is a monotonically increasing function, 
then write plain Haskell code to reify a paper-and-pencil-style proof 
for that theorem, that can be machine checked by LiquidHaskell.

<!-- more -->

<br>
<br>
<br>

<div class="row-fluid">
  <div class="span12 pagination-centered">
  <img src="https://eyesofodysseus.files.wordpress.com/2013/06/full-moon-over-ocean-reflection.jpg"
       alt="Reflection" width="300">
  </div>
</div>


<div class="hidden">

<pre><span class=hs-linenum>38: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--higherorder"</span>     <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>39: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--totality"</span>        <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>40: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>RefinementReflection</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>41: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>ProofCombinators</span>
<span class=hs-linenum>42: </span>
<span class=hs-linenum>43: </span><span class='hs-definition'>fib</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>44: </span><span class='hs-definition'>propPlusComm</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Proof</span> 
<span class=hs-linenum>45: </span><span class='hs-definition'>propOnePlueOne</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>()</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Proof</span> 
<span class=hs-linenum>46: </span><span class='hs-definition'>fibTwo</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>()</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Proof</span> 
<span class=hs-linenum>47: </span><span class='hs-definition'>fibCongruence</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Proof</span>
<span class=hs-linenum>48: </span><span class='hs-definition'>fibUp</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Proof</span> 
<span class=hs-linenum>49: </span><span class='hs-definition'>fibTwoPretty</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Proof</span> 
<span class=hs-linenum>50: </span><span class='hs-definition'>fibThree</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>()</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Proof</span> 
<span class=hs-linenum>51: </span><span class='hs-definition'>fMono</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span><span class='hs-layout'>)</span>
<span class=hs-linenum>52: </span>      <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Proof</span><span class='hs-layout'>)</span>
<span class=hs-linenum>53: </span>      <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>54: </span>      <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> 
<span class=hs-linenum>55: </span>      <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Proof</span> 
<span class=hs-linenum>56: </span><span class='hs-definition'>fibMono</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Proof</span> 
<span class=hs-linenum>57: </span>
</pre>
</div>

Shallow vs. Deep Specifications
-------------------------------

Up to now, we have been using Liquid Haskell to specify and verify "shallow"
specifications that abstractly describe the behavior of functions.  For example,
below, we specify and verify that `fib`restricted to natural numbers, always
terminates returning a natural number.


<pre><span class=hs-linenum>70: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fib</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Nat</span> <span class='hs-varop'>/</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>i</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>71: </span><a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0}</span><span class='hs-definition'>fib</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0}</span><span class='hs-varid'>i</span></a> <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>GHC.Types.Bool</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Bool | Prop v &lt;=&gt; x1 == x2}</span><span class='hs-varop'>==</span></a> <span class='hs-num'>0</span>    <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span> 
<span class=hs-linenum>72: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>GHC.Types.Bool</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Bool | Prop v &lt;=&gt; x1 == x2}</span><span class='hs-varop'>==</span></a> <span class='hs-num'>1</span>    <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> 
<span class=hs-linenum>73: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0}</span><span class='hs-varid'>fib</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0}</span><span class='hs-varid'>fib</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a><span class='hs-num'>2</span><span class='hs-layout'>)</span>
</pre>

In this post we present how refinement reflection is used to verify 
"deep" specifications that use the exact definition of Haskell functions. 
For example, we will prove that the Haskell `fib` function is increasing.



Propositions
------------

To begin with, we import [ProofCombinators][proofcomb], a (Liquid) Haskell 
library that defines and manipulates logical proofs. 


<pre><span class=hs-linenum>89: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>ProofCombinators</span>
</pre>

A `Proof` is a data type that carries no run time information


<pre><span class=hs-linenum>95: </span><span class='hs-keyword'>type</span> <span class='hs-conid'>Proof</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span>
</pre>

but can be refined with desired logical propositions.
For example, the following type states that `1 + 1 == 2`


<pre><span class=hs-linenum>102: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>OnePlusOne</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span> <span class='hs-conid'>Proof</span> <span class='hs-keyglyph'>|</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-num'>1</span> <span class='hs-varop'>==</span> <span class='hs-num'>2</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

Since the `v` and `Proof` are irrelevant, we may as well abbreviate 
the above to 


<pre><span class=hs-linenum>109: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>OnePlusOne'</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-num'>1</span> <span class='hs-varop'>==</span> <span class='hs-num'>2</span> <span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>


As another example, the following function type declares 
that _for each_ `x` and `y` the plus operator commutes. 


<pre><span class=hs-linenum>117: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>PlusComm</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>x</span> <span class='hs-varop'>+</span> <span class='hs-varid'>y</span> <span class='hs-varop'>==</span> <span class='hs-varid'>y</span> <span class='hs-varop'>+</span> <span class='hs-varid'>x</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span> 
</pre>



Trivial Proofs
--------------

We prove the above theorems using Haskell programs. 
The `ProofCombinators` module defines the `trivial` proof


<pre><span class=hs-linenum>129: </span><span class='hs-definition'>trivial</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Proof</span> 
<span class=hs-linenum>130: </span><span class='hs-definition'>trivial</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span>
</pre>

and the "casting" operator `(***)` that makes proof terms look 
nice:


<pre><span class=hs-linenum>137: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>QED</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>QED</span>
<span class=hs-linenum>138: </span>
<span class=hs-linenum>139: </span><span class='hs-layout'>(</span><span class='hs-varop'>***</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>QED</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Proof</span>
<span class=hs-linenum>140: </span><span class='hs-keyword'>_</span> <span class='hs-varop'>***</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span>
</pre>

Using the underlying SMT's knowledge on linear arithmetic, 
we can trivially prove the above propositions.


<pre><span class=hs-linenum>147: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>propOnePlueOne</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OnePlusOne</span> <span class='hs-keyword'>@-}</span> 
<span class=hs-linenum>148: </span><a class=annot href="#"><span class=annottext>() -&gt; {VV : () | 1 + 1 == 2}</span><span class='hs-definition'>propOnePlueOne</span></a> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : Language.Haskell.Liquid.ProofCombinators.QED | v == Language.Haskell.Liquid.ProofCombinators.QED}</span><span class='hs-varid'>trivial</span></a> <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span> 
<span class=hs-linenum>149: </span>
<span class=hs-linenum>150: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>propPlusComm</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>PlusComm</span> <span class='hs-keyword'>@-}</span> 
<span class=hs-linenum>151: </span><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {VV : () | x1 + x2 == x2 + x1}</span><span class='hs-definition'>propPlusComm</span></a> <span class='hs-keyword'>_</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : Language.Haskell.Liquid.ProofCombinators.QED | v == Language.Haskell.Liquid.ProofCombinators.QED}</span><span class='hs-varid'>trivial</span></a> <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span> 
</pre>


We saw how we use SMT's knowledge on linear arithmetic 
to trivially prove arithmetic properties. But how can 
we prove ``deep'' properties on Haskell's functions?


Refinement Reflection 
---------------------

Refinement Reflection allows deep specification and 
verification by reflecting the code implementing a Haskell
function into the function’s output refinement type.

Refinement Reflection proceeds in 3 steps: definition, reflection, and application.
Consider reflecting the definition of `fib` into the logic


<pre><span class=hs-linenum>171: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reflect</span> <span class='hs-varid'>fib</span> <span class='hs-keyword'>@-}</span>
</pre>

then the following three reflection steps will occur. 

Step 1: Definition 
------------------

Reflection of the Haskell function `fib` defines in logic 
an _uninterpreted_ function `fib` that satisfies the congruence axiom.

In the logic the function `fib` is defined.


<pre><span class=hs-linenum>185: </span><span class='hs-definition'>fib</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> 
</pre>

SMT only knows that `fib` satisfies the congruence axiom.


<pre><span class=hs-linenum>191: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fibCongruence</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{i == j =&gt; fib i == fib j}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>192: </span><a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; x2:{v : GHC.Types.Int | v &gt;= 0} -&gt; {VV : () | x1 == x2 =&gt; fib x1 == fib x2}</span><span class='hs-definition'>fibCongruence</span></a> <span class='hs-keyword'>_</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : Language.Haskell.Liquid.ProofCombinators.QED | v == Language.Haskell.Liquid.ProofCombinators.QED}</span><span class='hs-varid'>trivial</span></a> <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span> 
</pre>

Other than congruence, SMT knowns nothing for the function `fib`,
until reflection happens!


Step 2: Reflection
------------------

As a second step, Liquid Haskell connects the Haskell function `fib`
with the homonymous logical function, 
by reflecting the implementation of `fib` in its result type. 


The result type of `fib` is automatically strengthened to the following.


<pre><span class=hs-linenum>210: </span><span class='hs-definition'>fib</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>==</span> <span class='hs-varid'>fib</span> <span class='hs-varid'>i</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>fibP</span> <span class='hs-varid'>i</span> <span class='hs-layout'>}</span>
</pre>

That is, the result satisfies the `fibP` predicate
exactly reflecting the implementation of `fib`.


<pre><span class=hs-linenum>217: </span><span class='hs-definition'>fibP</span> <span class='hs-varid'>i</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>if</span> <span class='hs-varid'>i</span> <span class='hs-varop'>==</span> <span class='hs-num'>0</span> <span class='hs-keyword'>then</span> <span class='hs-num'>0</span> <span class='hs-keyword'>else</span>
<span class=hs-linenum>218: </span>         <span class='hs-keyword'>if</span> <span class='hs-varid'>i</span> <span class='hs-varop'>==</span> <span class='hs-num'>1</span> <span class='hs-keyword'>then</span> <span class='hs-num'>1</span> <span class='hs-keyword'>else</span>
<span class=hs-linenum>219: </span>         <span class='hs-varid'>fin</span> <span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-comment'>-</span><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varop'>+</span> <span class='hs-varid'>fib</span> <span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-comment'>-</span><span class='hs-num'>2</span><span class='hs-layout'>)</span>
</pre>

Step 3: Application 
-------------------

With the reflected refinement type,
each application of `fib` automatically unfolds the definition of `fib` 
once. 
As an example, applying `fib` to `0`, `1`, and `2` allows us to prove that `fib 2 == 1`:


<pre><span class=hs-linenum>231: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fibTwo</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{ fib 2 == 1 }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>232: </span><a class=annot href="#"><span class=annottext>() -&gt; {VV : () | fib 2 == 1}</span><span class='hs-definition'>fibTwo</span></a> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : [GHC.Types.Int] | null v &lt;=&gt; false}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>0</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>1</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>2</span><span class='hs-keyglyph'>]</span> <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
</pre>

Though valid, the above `fibTwo` proof is not pretty! 


Structuring Proofs 
------------------

To make our proofs look nice, we use combinators from 
the `ProofCombinators` library, which exports a family 
of operators `(*.)` where `*` comes from the theory of 
linear arithmetic and the refinement type of `x *. y` 

+ **requires** that `x *. y` holds and 
+ **ensures** that the returned value is equal to `x`.

For example, `(==.)` and `(<=.)` are predefined in `ProofCombinators` as


<pre><span class=hs-linenum>252: </span><span class='hs-layout'>(</span><span class='hs-varop'>==.</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-layout'>{</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>|</span> <span class='hs-varid'>x</span><span class='hs-varop'>==</span><span class='hs-varid'>y</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span><span class='hs-varop'>==</span><span class='hs-varid'>x</span><span class='hs-layout'>}</span>
<span class=hs-linenum>253: </span><span class='hs-definition'>x</span> <span class='hs-varop'>==.</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>x</span>
<span class=hs-linenum>254: </span>
<span class=hs-linenum>255: </span><span class='hs-layout'>(</span><span class='hs-varop'>&lt;=.</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-layout'>{</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>|</span> <span class='hs-varid'>x</span><span class='hs-varop'>&lt;=</span><span class='hs-varid'>y</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span><span class='hs-varop'>==</span><span class='hs-varid'>x</span><span class='hs-layout'>}</span>
<span class=hs-linenum>256: </span><span class='hs-definition'>x</span> <span class='hs-varop'>&lt;=.</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>x</span>
</pre>

Using these predefined operators, we construct paper and pencil-like proofs 
for the `fib` function.


<pre><span class=hs-linenum>263: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fibTwoPretty</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{ fib 2 == 1 }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>264: </span><a class=annot href="#"><span class=annottext>{VV : () | fib 2 == 1}</span><span class='hs-definition'>fibTwoPretty</span></a> 
<span class=hs-linenum>265: </span>  <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>2</span> 
<span class=hs-linenum>266: </span>  <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; GHC.Types.Int</span><span class='hs-varop'>==.</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>1</span> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>0</span> 
<span class=hs-linenum>267: </span>  <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
</pre>



Because operator 
-----------------

To allow the reuse of existing proofs, `ProofCombinators` defines the because 
operator `(∵)`


<pre><span class=hs-linenum>279: </span><span class='hs-layout'>(</span><span class='hs-varid'>∵</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Proof</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Proof</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>280: </span><span class='hs-definition'>f</span> <span class='hs-varid'>∵</span> <span class='hs-varid'>y</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>f</span> <span class='hs-varid'>y</span>
</pre>

For example, `fib 3 == 2` holds because `fib 2 == 1`:


<pre><span class=hs-linenum>286: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fibThree</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{ fib 3 == 2 }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>287: </span><a class=annot href="#"><span class=annottext>() -&gt; {VV : () | fib 3 == 2}</span><span class='hs-definition'>fibThree</span></a> <span class='hs-keyword'>_</span> 
<span class=hs-linenum>288: </span>  <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>3</span> 
<span class=hs-linenum>289: </span>  <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; GHC.Types.Int</span><span class='hs-varop'>==.</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>2</span> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>1</span>
<span class=hs-linenum>290: </span>  <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; () -&gt; GHC.Types.Int</span><span class='hs-varop'>==.</span></a> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-num'>1</span></a>     <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <span class='hs-num'>1</span>      <span class='hs-varid'>∵</span> <span class='hs-varid'>fibTwoPretty</span>
<span class=hs-linenum>291: </span>  <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; GHC.Types.Int</span><span class='hs-varop'>==.</span></a> <span class='hs-num'>2</span> 
<span class=hs-linenum>292: </span>  <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
</pre>



Proofs by Induction (i.e. Recursion) 
------------------------------------

Next, combining the above operators we specify and prove that 
`fib` is increasing, that is for each natural number `i`, 
`fib i <= fib (i+1)`. 

We specify the theorem as a refinement type for `fubUp`
and use Haskell code to persuade Liquid Haskell that 
the theorem holds. 


<pre><span class=hs-linenum>309: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fibUp</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{fib i &lt;= fib (i+1)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>310: </span><a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {VV : () | fib x1 &lt;= fib (x1 + 1)}</span><span class='hs-definition'>fibUp</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0}</span><span class='hs-varid'>i</span></a>
<span class=hs-linenum>311: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>GHC.Types.Bool</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Bool | Prop v &lt;=&gt; x1 == x2}</span><span class='hs-varop'>==</span></a> <span class='hs-num'>0</span>
<span class=hs-linenum>312: </span>  <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>0</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; GHC.Types.Int</span><span class='hs-varop'>&lt;.</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>1</span>
<span class=hs-linenum>313: </span>  <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
<span class=hs-linenum>314: </span>
<span class=hs-linenum>315: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>GHC.Types.Bool</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Bool | Prop v &lt;=&gt; x1 == x2}</span><span class='hs-varop'>==</span></a> <span class='hs-num'>1</span>
<span class=hs-linenum>316: </span>  <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>1</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; GHC.Types.Int</span><span class='hs-varop'>&lt;=.</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>1</span> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>0</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; GHC.Types.Int</span><span class='hs-varop'>&lt;=.</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-num'>2</span>
<span class=hs-linenum>317: </span>  <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
<span class=hs-linenum>318: </span>
<span class=hs-linenum>319: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>
<span class=hs-linenum>320: </span>  <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-varid'>i</span>
<span class=hs-linenum>321: </span>  <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; GHC.Types.Int</span><span class='hs-varop'>==.</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a><span class='hs-num'>2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>322: </span>  <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; () -&gt; GHC.Types.Int</span><span class='hs-varop'>&lt;=.</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-varid'>i</span>     <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a><span class='hs-num'>2</span><span class='hs-layout'>)</span> <span class='hs-varid'>∵</span> <a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {VV : () | fib x1 &lt;= fib (x1 + 1)}</span><span class='hs-varid'>fibUp</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span>
<span class=hs-linenum>323: </span>  <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; () -&gt; GHC.Types.Int</span><span class='hs-varop'>&lt;=.</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-varid'>i</span>     <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varid'>∵</span> <a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {VV : () | fib x1 &lt;= fib (x1 + 1)}</span><span class='hs-varid'>fibUp</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a><span class='hs-num'>2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>324: </span>  <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; GHC.Types.Int</span><span class='hs-varop'>&lt;=.</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span>
<span class=hs-linenum>325: </span>  <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
</pre>

The proof proceeds _by induction on_ `i`. 

+ The base cases `i == 0` and `i == 1` are represented 
  as Haskell's case splitting. 

+ The inductive hypothesis is represented by recursive calls 
  on smaller inputs. 

Finally, the SMT solves arithmetic reasoning to conclude the proof.  

Higher Order Theorems
----------------------

Refinement Reflection can be used to express and verify higher order theorems!
For example, `fMono` specifies that each locally increasing function is monotonic! 


<pre><span class=hs-linenum>345: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fMono</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>f</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span><span class='hs-layout'>)</span>
<span class=hs-linenum>346: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>fUp</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-varid'>z</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{f z &lt;= f (z+1)}</span><span class='hs-layout'>)</span>
<span class=hs-linenum>347: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span>
<span class=hs-linenum>348: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-keyword'>{Nat|x &lt; y}</span>
<span class=hs-linenum>349: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{f x &lt;= f y}</span> <span class='hs-varop'>/</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>y</span><span class='hs-keyglyph'>]</span> 
<span class=hs-linenum>350: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>351: </span><a class=annot href="#"><span class=annottext>x1:({v : GHC.Types.Int | v &gt;= 0} -&gt; GHC.Types.Int) -&gt; (x4:{v : GHC.Types.Int | v &gt;= 0} -&gt; {VV : () | x1 x4 &lt;= x1 (x4 + 1)}) -&gt; x5:{v : GHC.Types.Int | v &gt;= 0} -&gt; x6:{v : GHC.Types.Int | v &gt;= 0
                                                                                                                                                                                          &amp;&amp; x5 &lt; v} -&gt; {VV : () | x1 x5 &lt;= x1 x6}</span><span class='hs-definition'>fMono</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0} -&gt; GHC.Types.Int</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {VV : () | f x1 &lt;= f (x1 + 1)}</span><span class='hs-varid'>thm</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0
                     &amp;&amp; x &lt; v}</span><span class='hs-varid'>y</span></a>  
<span class=hs-linenum>352: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <span class='hs-num'>1</span> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Bool | Prop v &lt;=&gt; x1 == x2}</span><span class='hs-varop'>==</span></a> <span class='hs-varid'>y</span>
<span class=hs-linenum>353: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : {v : GHC.Types.Int | v &gt;= 0} -&gt; GHC.Types.Int | v == f}</span><span class='hs-varid'>f</span></a> <span class='hs-varid'>y</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; GHC.Types.Int</span><span class='hs-varop'>==.</span></a> <a class=annot href="#"><span class=annottext>{v : {v : GHC.Types.Int | v &gt;= 0} -&gt; GHC.Types.Int | v == f}</span><span class='hs-varid'>f</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <span class='hs-num'>1</span><span class='hs-layout'>)</span>
<span class=hs-linenum>354: </span>         <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; () -&gt; GHC.Types.Int</span><span class='hs-varop'>&gt;.</span></a> <a class=annot href="#"><span class=annottext>{v : {v : GHC.Types.Int | v &gt;= 0} -&gt; GHC.Types.Int | v == f}</span><span class='hs-varid'>f</span></a> <span class='hs-varid'>x</span>       <span class='hs-varid'>∵</span> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : () | f x1 &lt;= f (x1 + 1)} | v == thm}</span><span class='hs-varid'>thm</span></a> <span class='hs-varid'>x</span>
<span class=hs-linenum>355: </span>        <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
<span class=hs-linenum>356: </span>
<span class=hs-linenum>357: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <span class='hs-num'>1</span> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Bool | Prop v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>y</span>
<span class=hs-linenum>358: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : {v : GHC.Types.Int | v &gt;= 0} -&gt; GHC.Types.Int | v == f}</span><span class='hs-varid'>f</span></a> <span class='hs-varid'>x</span>
<span class=hs-linenum>359: </span>  <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; () -&gt; GHC.Types.Int</span><span class='hs-varop'>&lt;.</span></a>  <a class=annot href="#"><span class=annottext>{v : {v : GHC.Types.Int | v &gt;= 0} -&gt; GHC.Types.Int | v == f}</span><span class='hs-varid'>f</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>y</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span>         <span class='hs-varid'>∵</span> <a class=annot href="#"><span class=annottext>x1:({v : GHC.Types.Int | v &gt;= 0} -&gt; GHC.Types.Int) -&gt; (x4:{v : GHC.Types.Int | v &gt;= 0} -&gt; {VV : () | x1 x4 &lt;= x1 (x4 + 1)}) -&gt; x5:{v : GHC.Types.Int | v &gt;= 0} -&gt; x6:{v : GHC.Types.Int | v &gt;= 0
                                                                                                                                                                                          &amp;&amp; x5 &lt; v} -&gt; {VV : () | x1 x5 &lt;= x1 x6}</span><span class='hs-varid'>fMono</span></a> <a class=annot href="#"><span class=annottext>{v : {v : GHC.Types.Int | v &gt;= 0} -&gt; GHC.Types.Int | v == f}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : () | f x1 &lt;= f (x1 + 1)} | v == thm}</span><span class='hs-varid'>thm</span></a> <span class='hs-varid'>x</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>y</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span>
<span class=hs-linenum>360: </span>  <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; GHC.Types.Int -&gt; () -&gt; GHC.Types.Int</span><span class='hs-varop'>&lt;.</span></a>  <a class=annot href="#"><span class=annottext>{v : {v : GHC.Types.Int | v &gt;= 0} -&gt; GHC.Types.Int | v == f}</span><span class='hs-varid'>f</span></a> <span class='hs-varid'>y</span>             <span class='hs-varid'>∵</span> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : () | f x1 &lt;= f (x1 + 1)} | v == thm}</span><span class='hs-varid'>thm</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>y</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span>
<span class=hs-linenum>361: </span>  <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
</pre>

Again, the recursive implementation of `fMono` depicts the paper and pencil 
proof of `fMono` by induction on the decreasing argument `/ [y]`. 

Since `fib` is proven to be locally increasing by `fUp`, we use `fMono` 
to prove that `fib` is monotonic. 


<pre><span class=hs-linenum>371: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fibMono</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>m</span><span class='hs-conop'>:</span><span class='hs-keyword'>{Nat | n &lt; m }</span>  <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{fib n &lt;= fib m}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>372: </span><a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; x2:{v : GHC.Types.Int | v &gt;= 0
                                                           &amp;&amp; x1 &lt; v} -&gt; {VV : () | fib x1 &lt;= fib x2}</span><span class='hs-definition'>fibMono</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:({v : GHC.Types.Int | v &gt;= 0} -&gt; GHC.Types.Int) -&gt; (x4:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : () | x1 x4 &lt;= x1 (x4 + 1)}) -&gt; x5:{v : GHC.Types.Int | v &gt;= 0} -&gt; x6:{v : GHC.Types.Int | v &gt;= 0
                                                                                                                                                                                              &amp;&amp; x5 &lt; v} -&gt; {v : () | x1 x5 &lt;= x1 x6} | v == RefinementReflection.fMono}</span><span class='hs-varid'>fMono</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                             &amp;&amp; v == fib x1
                                                             &amp;&amp; v == (if x1 == 0 then 0 else (if x1 == 1 then 1 else fib (x1 - 1) + fib (x1 - 2)))} | v == fib}</span><span class='hs-varid'>fib</span></a> <a class=annot href="#"><span class=annottext>{v : x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; {v : () | fib x1 &lt;= fib (x1 + 1)} | v == RefinementReflection.fibUp}</span><span class='hs-varid'>fibUp</span></a>
</pre>


Conclusion
----------

We saw how refinement reflection turns Haskell
into a theorem prover by reflecting the code 
implementing a Haskell function into the 
function’s output refinement type.

Refinement Types are used to express theorems, 
Haskell code is used to prove such theorems
expressing paper pencil proofs, and Liquid Haskell 
verifies the validity of the proofs!

Proving `fib` monotonic is great, but this is Haskell!
Wouldn’t it be nice to prove theorems about inductive data types 
and higher order functions? Like fusions and folds? 
Or program equivalence on run-time optimizations like map-reduce?

Stay tuned!

Even better, if you happen you be in Nara for ICFP'16, 
come to my [CUFP tutorial][cufp16] for more!


[cufp16]: http://cufp.org/2016/t6-niki-vazou-liquid-haskell-intro.html
[proofcomb]:https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/ProofCombinators.hs
