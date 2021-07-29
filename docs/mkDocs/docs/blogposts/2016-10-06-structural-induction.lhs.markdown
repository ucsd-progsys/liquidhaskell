---
layout: post
title: Refinement Reflection on ADTs
date: 2016-10-06
comments: true
author: Niki Vazou
published: true
tags: reflection, induction, measures
demo: MonoidList.hs
---

Lists are Monoids
-----------------

[Previously][refinement-reflection] we saw how Refinement Reflection
can be used to write Haskell functions that prove theorems about
other Haskell functions. Today, we will see how Refinement Reflection
works on **recursive data types**.
As an example, we will prove that **lists are monoids** (under nil and append).

Lets see how to express **the monoid laws** as liquid types, and then prove
the laws by writing plain Haskell functions that are checked by LiquidHaskell.

<!-- more -->

<br>

<div class="row-fluid">
  <div class="span12 pagination-centered">
  <p style="text-align:center">
  <img class="center-block" src="http://www.aaronartprints.org/images/Paintings/4597.jpg" alt="Recursion" width="300">
       <br>
       Recursive Paper and Pencil Proofs.
       "Drawing Hands" by Escher.
       <br>
  </p>
  </div>
</div>


<div class="hidden">

<pre><span class=hs-linenum>46: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--higherorder"</span>     <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>47: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--totality"</span>        <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>48: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>StructuralInduction</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>49: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>ProofCombinators</span>
<span class=hs-linenum>50: </span>
<span class=hs-linenum>51: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>length</span><span class='hs-layout'>)</span>
<span class=hs-linenum>52: </span>
<span class=hs-linenum>53: </span><span class='hs-definition'>length</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>54: </span><span class='hs-definition'>leftId</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Proof</span>
<span class=hs-linenum>55: </span><span class='hs-definition'>rightId</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Proof</span>
<span class=hs-linenum>56: </span><span class='hs-definition'>associativity</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Proof</span>
</pre>
</div>

Lists
-----

First, lets define the `List a` data type


<pre><span class=hs-linenum>66: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>|</span> <span class='hs-conid'>C</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
</pre>

Induction on Lists
------------------

As we will see, *proofs* by structural induction will correspond to
*programs* that perform recursion on lists. To keep things legit,
we must verify that those programs are total and terminating.

To that end, lets define a `length` function that
computes the natural number that is the size of a
list.


<pre><span class=hs-linenum>81: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>length</span>               <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>82: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>length</span>      <span class='hs-keyglyph'>::</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Nat</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>83: </span><a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; {v : GHC.Types.Int | v &gt;= 0
                                                        &amp;&amp; v == length x1}</span><span class='hs-definition'>length</span></a> <span class='hs-conid'>N</span>        <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span>
<span class=hs-linenum>84: </span><span class='hs-definition'>length</span> <span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == (1 : int)}</span><span class='hs-num'>1</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0
                     &amp;&amp; v == length xs
                     &amp;&amp; v == length xs}</span><span class='hs-varid'>length</span></a> <span class='hs-varid'>xs</span>
</pre>

We lift `length` in the logic, as a [measure][the-advantage-of-measures].

We can now tell Liquid Haskell that when proving termination
on recursive functions with a list argument `xs`, it should
check whether the `length xs` is decreasing.


<pre><span class=hs-linenum>94: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>List</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>length</span><span class='hs-keyglyph'>]</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>|</span> <span class='hs-conid'>C</span> <span class='hs-layout'>{</span><span class='hs-varid'>hd</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>,</span> <span class='hs-varid'>tl</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>


Reflecting Lists into the Logic
-------------------------------

To talk about lists in the logic, we use the annotation


<pre><span class=hs-linenum>104: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--exact-data-cons"</span> <span class='hs-keyword'>@-}</span>
</pre>

which **automatically** derives measures for

* *testing* if a value has a given data constructor, and
* *extracting* the corresponding field's value.

For our example, LH will automatically derive the following
functions in the refinement logic.


<pre><span class=hs-linenum>116: </span><span class='hs-definition'>isN</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>         <span class='hs-comment'>-- Haskell's null</span>
<span class=hs-linenum>117: </span><span class='hs-definition'>isC</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>         <span class='hs-comment'>-- Haskell's not . null</span>
<span class=hs-linenum>118: </span>
<span class=hs-linenum>119: </span><span class='hs-definition'>select_C_1</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>     <span class='hs-comment'>-- Haskell's head</span>
<span class=hs-linenum>120: </span><span class='hs-definition'>select_C_2</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span>   <span class='hs-comment'>-- Haskell's tail</span>
</pre>

A programmer *never* sees the above operators; they are internally
used by LH to **reflect** Haskell functions into the refinement logic,
as we shall see shortly.

Defining the Monoid Operators
-----------------------------

A structure is a monoid, when it has two operators:

* the identity element `empty` and
* an associative operator `<>`.

Lets define these two operators for our `List`.

* the identity element is the empty list, and
* the associative operator `<>` is list append.


<pre><span class=hs-linenum>141: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reflect</span> <span class='hs-varid'>empty</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>142: </span><span class='hs-definition'>empty</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>143: </span><a class=annot href="#"><span class=annottext>{VV : (StructuralInduction.List a) | VV == empty
                                     &amp;&amp; VV == StructuralInduction.N}</span><span class='hs-definition'>empty</span></a>  <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span>
<span class=hs-linenum>144: </span>
<span class=hs-linenum>145: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>infix</span>   <span class='hs-varop'>&lt;&gt;</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>146: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reflect</span> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>147: </span><span class='hs-layout'>(</span><span class='hs-varop'>&lt;&gt;</span><span class='hs-layout'>)</span>           <span class='hs-keyglyph'>::</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>148: </span><span class='hs-conid'>N</span>        <a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; x2:(StructuralInduction.List a) -&gt; {VV : (StructuralInduction.List a) | VV == &lt;&gt; x1 x2
                                                                                                           &amp;&amp; VV == (if is_N x1 then x2 else StructuralInduction.C (select_C_1 x1) (&lt;&gt; (select_C_2 x1) x2))}</span><span class='hs-varop'>&lt;&gt;</span></a> <a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-varid'>ys</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>ys</span>
<span class=hs-linenum>149: </span><span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>ys</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; {v : (StructuralInduction.List a) | tl v == x1
                                                                       &amp;&amp; hd v == x
                                                                       &amp;&amp; select_C_2 v == x1
                                                                       &amp;&amp; select_C_1 v == x
                                                                       &amp;&amp; (is_C v &lt;=&gt; true)
                                                                       &amp;&amp; (is_N v &lt;=&gt; false)
                                                                       &amp;&amp; length v == 1 + length x1
                                                                       &amp;&amp; v == StructuralInduction.C x x1}</span><span class='hs-conid'>C</span></a> <span class='hs-varid'>x</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (StructuralInduction.List a) | VV == &lt;&gt; xs ys
                                     &amp;&amp; VV == (if is_N xs then ys else StructuralInduction.C (select_C_1 xs) (&lt;&gt; (select_C_2 xs) ys))
                                     &amp;&amp; VV == &lt;&gt; xs ys}</span><span class='hs-varid'>xs</span></a> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span>
</pre>

LiquidHaskell automatically checked that the recursive `(<>)`
is terminating, by checking that the `length` of its first
argument is decreasing. Since both the above operators are
provably terminating, LH lets us reflect them into logic.

As with our [previous][refinement-reflection]
`fibonacci` example, reflection of a function
into logic, means strengthening the result type
of the function with its implementation.

Thus, the **automatically** derived, strengthened
types for `empty` and `(<>)` will be


<pre><span class=hs-linenum>166: </span><span class='hs-definition'>empty</span>   <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>==</span> <span class='hs-varid'>empty</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>v</span> <span class='hs-varop'>==</span> <span class='hs-conid'>N</span> <span class='hs-layout'>}</span>
<span class=hs-linenum>167: </span>
<span class=hs-linenum>168: </span><span class='hs-layout'>(</span><span class='hs-varop'>&lt;&gt;</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>169: </span>     <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>==</span> <span class='hs-varid'>xs</span> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>ys</span> <span class='hs-varop'>&amp;&amp;</span>
<span class=hs-linenum>170: </span>                    <span class='hs-varid'>v</span> <span class='hs-varop'>==</span> <span class='hs-keyword'>if</span> <span class='hs-varid'>isN</span> <span class='hs-varid'>xs</span> <span class='hs-keyword'>then</span> <span class='hs-varid'>ys</span> <span class='hs-keyword'>else</span>
<span class=hs-linenum>171: </span>                         <span class='hs-conid'>C</span> <span class='hs-layout'>(</span><span class='hs-varid'>select_C_1</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>select_C_2</span> <span class='hs-varid'>xs</span> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span>
<span class=hs-linenum>172: </span>        <span class='hs-layout'>}</span>
</pre>

In effect, the derived checker and selector functions are used
to translate Haskell to logic. The above is just to *explain*
how LH reasons about the operators; the programmer never (directly)
reads or writes the operators `isN` or `select_C_1` etc.

Proving the Monoid Laws
------------------------

Finally, we have set everything up, (actually LiquidHaskell
did most of the work for us) and we are ready to prove the
monoid laws for the `List`.

First we prove left identity of `empty`.


<pre><span class=hs-linenum>190: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>leftId</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{ empty &lt;&gt; x == x }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>191: </span><a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; {VV : () | &lt;&gt; empty x1 == x1}</span><span class='hs-definition'>leftId</span></a> <a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>192: </span>   <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-varid'>empty</span></a> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>x</span>
<span class=hs-linenum>193: </span>   <a class=annot href="#"><span class=annottext>(StructuralInduction.List a) -&gt; (StructuralInduction.List a) -&gt; (StructuralInduction.List a)</span><span class='hs-varop'>==.</span></a> <a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-conid'>N</span></a> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>x</span>
<span class=hs-linenum>194: </span>   <a class=annot href="#"><span class=annottext>(StructuralInduction.List a) -&gt; (StructuralInduction.List a) -&gt; (StructuralInduction.List a)</span><span class='hs-varop'>==.</span></a> <span class='hs-varid'>x</span>
<span class=hs-linenum>195: </span>   <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
</pre>

This proof was trivial, because left identity is satisfied
by the way we defined `(<>)`.

Next, we prove right identity of `empty`.


<pre><span class=hs-linenum>204: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>rightId</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{ x &lt;&gt; empty  == x }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>205: </span><a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; {VV : () | &lt;&gt; x1 empty == x1}</span><span class='hs-definition'>rightId</span></a> <span class='hs-conid'>N</span>
<span class=hs-linenum>206: </span>   <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>(StructuralInduction.List (GHC.Prim.Any *))</span><span class='hs-conid'>N</span></a> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>empty</span>
<span class=hs-linenum>207: </span>   <a class=annot href="#"><span class=annottext>(StructuralInduction.List (GHC.Prim.Any *)) -&gt; (StructuralInduction.List (GHC.Prim.Any *)) -&gt; (StructuralInduction.List (GHC.Prim.Any *))</span><span class='hs-varop'>==.</span></a> <span class='hs-conid'>N</span>
<span class=hs-linenum>208: </span>   <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
<span class=hs-linenum>209: </span>
<span class=hs-linenum>210: </span><span class='hs-definition'>rightId</span> <span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>211: </span>   <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; {v : (StructuralInduction.List a) | tl v == x1
                                                                       &amp;&amp; hd v == x
                                                                       &amp;&amp; select_C_2 v == x1
                                                                       &amp;&amp; select_C_1 v == x
                                                                       &amp;&amp; (is_C v &lt;=&gt; true)
                                                                       &amp;&amp; (is_N v &lt;=&gt; false)
                                                                       &amp;&amp; length v == 1 + length x1
                                                                       &amp;&amp; v == StructuralInduction.C x x1}</span><span class='hs-conid'>C</span></a> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>empty</span>
<span class=hs-linenum>212: </span>   <a class=annot href="#"><span class=annottext>(StructuralInduction.List a) -&gt; (StructuralInduction.List a) -&gt; (StructuralInduction.List a)</span><span class='hs-varop'>==.</span></a> <a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; {v : (StructuralInduction.List a) | tl v == x1
                                                                       &amp;&amp; hd v == x
                                                                       &amp;&amp; select_C_2 v == x1
                                                                       &amp;&amp; select_C_1 v == x
                                                                       &amp;&amp; (is_C v &lt;=&gt; true)
                                                                       &amp;&amp; (is_N v &lt;=&gt; false)
                                                                       &amp;&amp; length v == 1 + length x1
                                                                       &amp;&amp; v == StructuralInduction.C x x1}</span><span class='hs-conid'>C</span></a> <span class='hs-varid'>x</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-varid'>xs</span></a> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>empty</span><span class='hs-layout'>)</span>
<span class=hs-linenum>213: </span>   <a class=annot href="#"><span class=annottext>(StructuralInduction.List a) -&gt; (StructuralInduction.List a) -&gt; () -&gt; (StructuralInduction.List a)</span><span class='hs-varop'>==.</span></a> <a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; {v : (StructuralInduction.List a) | tl v == x1
                                                                       &amp;&amp; hd v == x
                                                                       &amp;&amp; select_C_2 v == x1
                                                                       &amp;&amp; select_C_1 v == x
                                                                       &amp;&amp; (is_C v &lt;=&gt; true)
                                                                       &amp;&amp; (is_N v &lt;=&gt; false)
                                                                       &amp;&amp; length v == 1 + length x1
                                                                       &amp;&amp; v == StructuralInduction.C x x1}</span><span class='hs-conid'>C</span></a> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span>        <span class='hs-varid'>∵</span> <a class=annot href="#"><span class=annottext>{VV : () | &lt;&gt; xs empty == xs}</span><span class='hs-varid'>rightId</span></a> <span class='hs-varid'>xs</span>
<span class=hs-linenum>214: </span>   <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
</pre>

This proof is more tricky, as it requires **structural induction** which is
encoded in LH proofs simply as **recursion**.  LH ensures that the inductive
hypothesis is appropriately applied by checking that the recursive proof is
total and terminating.  In the `rightId` case, for termination, Liquid Haskell
checked that `length xs < length (C x xs)`.

It turns out that we can prove lots of properties about lists using structural
induction, encoded in Haskell as

* case splitting,
* recursive calls, and
* rewriting,

To see a last example, lets prove the associativity of `(<>)`.


<pre><span class=hs-linenum>233: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>associativity</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>z</span><span class='hs-conop'>:</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>234: </span>                  <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{ x &lt;&gt; (y &lt;&gt; z) == (x &lt;&gt; y) &lt;&gt; z }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>235: </span><a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; x2:(StructuralInduction.List a) -&gt; x3:(StructuralInduction.List a) -&gt; {VV : () | &lt;&gt; x1 (&lt;&gt; x2 x3) == &lt;&gt; (&lt;&gt; x1 x2) x3}</span><span class='hs-definition'>associativity</span></a> <span class='hs-conid'>N</span> <a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-varid'>z</span></a>
<span class=hs-linenum>236: </span>  <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-conid'>N</span></a> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : (StructuralInduction.List a) | v == &lt;&gt; y z
                                    &amp;&amp; v == (if is_N y then z else StructuralInduction.C (select_C_1 y) (&lt;&gt; (select_C_2 y) z))
                                    &amp;&amp; v == &lt;&gt; y z}</span><span class='hs-varid'>y</span></a> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>z</span><span class='hs-layout'>)</span>
<span class=hs-linenum>237: </span>  <a class=annot href="#"><span class=annottext>(StructuralInduction.List a) -&gt; (StructuralInduction.List a) -&gt; (StructuralInduction.List a)</span><span class='hs-varop'>==.</span></a> <a class=annot href="#"><span class=annottext>{v : (StructuralInduction.List a) | v == &lt;&gt; y z
                                    &amp;&amp; v == (if is_N y then z else StructuralInduction.C (select_C_1 y) (&lt;&gt; (select_C_2 y) z))
                                    &amp;&amp; v == &lt;&gt; y z}</span><span class='hs-varid'>y</span></a> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>z</span>
<span class=hs-linenum>238: </span>  <a class=annot href="#"><span class=annottext>(StructuralInduction.List a) -&gt; (StructuralInduction.List a) -&gt; (StructuralInduction.List a)</span><span class='hs-varop'>==.</span></a> <a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-conid'>N</span></a> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>y</span><span class='hs-layout'>)</span> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>z</span>
<span class=hs-linenum>239: </span>  <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
<span class=hs-linenum>240: </span>
<span class=hs-linenum>241: </span><span class='hs-definition'>associativity</span> <span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varid'>y</span> <span class='hs-varid'>z</span>
<span class=hs-linenum>242: </span>  <span class='hs-keyglyph'>=</span>  <a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; {v : (StructuralInduction.List a) | tl v == x1
                                                                       &amp;&amp; hd v == x
                                                                       &amp;&amp; select_C_2 v == x1
                                                                       &amp;&amp; select_C_1 v == x
                                                                       &amp;&amp; (is_C v &lt;=&gt; true)
                                                                       &amp;&amp; (is_N v &lt;=&gt; false)
                                                                       &amp;&amp; length v == 1 + length x1
                                                                       &amp;&amp; v == StructuralInduction.C x x1}</span><span class='hs-conid'>C</span></a> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : (StructuralInduction.List a) | v == &lt;&gt; y z
                                    &amp;&amp; v == (if is_N y then z else StructuralInduction.C (select_C_1 y) (&lt;&gt; (select_C_2 y) z))
                                    &amp;&amp; v == &lt;&gt; y z}</span><span class='hs-varid'>y</span></a> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>z</span><span class='hs-layout'>)</span>
<span class=hs-linenum>243: </span>  <a class=annot href="#"><span class=annottext>(StructuralInduction.List a) -&gt; (StructuralInduction.List a) -&gt; (StructuralInduction.List a)</span><span class='hs-varop'>==.</span></a> <a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; {v : (StructuralInduction.List a) | tl v == x1
                                                                       &amp;&amp; hd v == x
                                                                       &amp;&amp; select_C_2 v == x1
                                                                       &amp;&amp; select_C_1 v == x
                                                                       &amp;&amp; (is_C v &lt;=&gt; true)
                                                                       &amp;&amp; (is_N v &lt;=&gt; false)
                                                                       &amp;&amp; length v == 1 + length x1
                                                                       &amp;&amp; v == StructuralInduction.C x x1}</span><span class='hs-conid'>C</span></a> <span class='hs-varid'>x</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-varid'>xs</span></a> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : (StructuralInduction.List a) | v == &lt;&gt; y z
                                    &amp;&amp; v == (if is_N y then z else StructuralInduction.C (select_C_1 y) (&lt;&gt; (select_C_2 y) z))
                                    &amp;&amp; v == &lt;&gt; y z}</span><span class='hs-varid'>y</span></a> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>z</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>244: </span>  <a class=annot href="#"><span class=annottext>(StructuralInduction.List a) -&gt; (StructuralInduction.List a) -&gt; () -&gt; (StructuralInduction.List a)</span><span class='hs-varop'>==.</span></a> <a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; {v : (StructuralInduction.List a) | tl v == x1
                                                                       &amp;&amp; hd v == x
                                                                       &amp;&amp; select_C_2 v == x1
                                                                       &amp;&amp; select_C_1 v == x
                                                                       &amp;&amp; (is_C v &lt;=&gt; true)
                                                                       &amp;&amp; (is_N v &lt;=&gt; false)
                                                                       &amp;&amp; length v == 1 + length x1
                                                                       &amp;&amp; v == StructuralInduction.C x x1}</span><span class='hs-conid'>C</span></a> <span class='hs-varid'>x</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{v : (StructuralInduction.List a) | v == &lt;&gt; xs y
                                    &amp;&amp; v == (if is_N xs then y else StructuralInduction.C (select_C_1 xs) (&lt;&gt; (select_C_2 xs) y))
                                    &amp;&amp; v == &lt;&gt; xs y}</span><span class='hs-varid'>xs</span></a> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>y</span><span class='hs-layout'>)</span> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>z</span><span class='hs-layout'>)</span> <span class='hs-varid'>∵</span> <a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; x2:(StructuralInduction.List a) -&gt; x3:(StructuralInduction.List a) -&gt; {VV : () | &lt;&gt; x1 (&lt;&gt; x2 x3) == &lt;&gt; (&lt;&gt; x1 x2) x3}</span><span class='hs-varid'>associativity</span></a> <span class='hs-varid'>xs</span> <span class='hs-varid'>y</span> <span class='hs-varid'>z</span>
<span class=hs-linenum>245: </span>  <a class=annot href="#"><span class=annottext>(StructuralInduction.List a) -&gt; (StructuralInduction.List a) -&gt; (StructuralInduction.List a)</span><span class='hs-varop'>==.</span></a> <a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; {v : (StructuralInduction.List a) | tl v == x1
                                                                       &amp;&amp; hd v == x
                                                                       &amp;&amp; select_C_2 v == x1
                                                                       &amp;&amp; select_C_1 v == x
                                                                       &amp;&amp; (is_C v &lt;=&gt; true)
                                                                       &amp;&amp; (is_N v &lt;=&gt; false)
                                                                       &amp;&amp; length v == 1 + length x1
                                                                       &amp;&amp; v == StructuralInduction.C x x1}</span><span class='hs-conid'>C</span></a> <span class='hs-varid'>x</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : (StructuralInduction.List a) | v == &lt;&gt; xs y
                                    &amp;&amp; v == (if is_N xs then y else StructuralInduction.C (select_C_1 xs) (&lt;&gt; (select_C_2 xs) y))
                                    &amp;&amp; v == &lt;&gt; xs y}</span><span class='hs-varid'>xs</span></a> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>y</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>z</span>
<span class=hs-linenum>246: </span>  <a class=annot href="#"><span class=annottext>(StructuralInduction.List a) -&gt; (StructuralInduction.List a) -&gt; (StructuralInduction.List a)</span><span class='hs-varop'>==.</span></a> <a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>(StructuralInduction.List a)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>x1:(StructuralInduction.List a) -&gt; {v : (StructuralInduction.List a) | tl v == x1
                                                                       &amp;&amp; hd v == x
                                                                       &amp;&amp; select_C_2 v == x1
                                                                       &amp;&amp; select_C_1 v == x
                                                                       &amp;&amp; (is_C v &lt;=&gt; true)
                                                                       &amp;&amp; (is_N v &lt;=&gt; false)
                                                                       &amp;&amp; length v == 1 + length x1
                                                                       &amp;&amp; v == StructuralInduction.C x x1}</span><span class='hs-conid'>C</span></a> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>y</span><span class='hs-layout'>)</span> <span class='hs-varop'>&lt;&gt;</span> <span class='hs-varid'>z</span>
<span class=hs-linenum>247: </span>  <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
</pre>

The above proof of associativity reifies the paper and pencil
proof by structural induction.

With that, we can safely conclude that our user defined list
is a monoid!


Conclusion
----------

We saw how Refinement Reflection can be used to

- specify properties of `ADTs`,
- naturally encode structural inductive proofs of these properties, and
- have these proofs machine checked by Liquid Haskell.

Why is this useful? Because the theorems we prove refer to your Haskell
functions!  Thus you (or in the future, the compiler) can use properties like
monoid or monad laws to optimize your Haskell code.  In the future, we will
present examples of code optimizations using monoid laws. Stay tuned!


[refinement-reflection]: http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2016/09/18/refinement-reflection.lhs/
[the-advantage-of-measures]: http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2014/02/11/the-advantage-of-measures.lhs/
