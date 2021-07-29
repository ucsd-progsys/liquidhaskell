---
layout: post
title: The Advantage of Measures
date: 2014-02-11
author: Eric Seidel
published: true
comments: true
tags: basic, measures
demo: SimpleRefinements.hs
---

Yesterday someone asked on [Reddit][] how one might define GHC's [OrdList][] 
in a way that statically enforces its three key invariants. The accepted
solution required rewriting `OrdList` as a `GADT` indexed by a proof of
*emptiness* (which is essentially created by a run-time check), and used
the new Closed Type Families extension in GHC 7.8 to define a type-level 
join of the Emptiness index.

Today, let's see a somewhat more direct way of tackling this problem in 
LiquidHaskell, in which we need not change a single line of code 
(well.. maybe one), and need not perform any dynamic checks. 

<!-- more -->

<div class="hidden">

<pre><span class=hs-linenum>27: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>OrdList</span><span class='hs-layout'>(</span>
<span class=hs-linenum>28: </span>    <span class='hs-conid'>OrdList</span><span class='hs-layout'>,</span> 
<span class=hs-linenum>29: </span>        <span class='hs-varid'>nilOL</span><span class='hs-layout'>,</span> <span class='hs-varid'>isNilOL</span><span class='hs-layout'>,</span> <span class='hs-varid'>unitOL</span><span class='hs-layout'>,</span> <span class='hs-varid'>appOL</span><span class='hs-layout'>,</span> <span class='hs-varid'>consOL</span><span class='hs-layout'>,</span> <span class='hs-varid'>snocOL</span><span class='hs-layout'>,</span> <span class='hs-varid'>concatOL</span><span class='hs-layout'>,</span>
<span class=hs-linenum>30: </span>        <span class='hs-varid'>mapOL</span><span class='hs-layout'>,</span> <span class='hs-varid'>fromOL</span><span class='hs-layout'>,</span> <span class='hs-varid'>toOL</span><span class='hs-layout'>,</span> <span class='hs-varid'>foldrOL</span><span class='hs-layout'>,</span> <span class='hs-varid'>foldlOL</span><span class='hs-layout'>,</span> <span class='hs-varid'>foldr'</span><span class='hs-layout'>,</span> <span class='hs-varid'>concatOL'</span>
<span class=hs-linenum>31: </span><span class='hs-layout'>)</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>32: </span>
<span class=hs-linenum>33: </span><span class='hs-keyword'>infixl</span> <span class='hs-num'>5</span>  <span class='hs-varop'>`appOL`</span>
<span class=hs-linenum>34: </span><span class='hs-keyword'>infixl</span> <span class='hs-num'>5</span>  <span class='hs-varop'>`snocOL`</span>
<span class=hs-linenum>35: </span><span class='hs-keyword'>infixr</span> <span class='hs-num'>5</span>  <span class='hs-varop'>`consOL`</span>
<span class=hs-linenum>36: </span><span class='hs-comment'>-- UGH parsing issues...</span>
<span class=hs-linenum>37: </span><span class='hs-keyword'>{-@</span>
<span class=hs-linenum>38: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>OrdList</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>olen</span><span class='hs-keyglyph'>]</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>None</span>
<span class=hs-linenum>39: </span>                      <span class='hs-keyglyph'>|</span> <span class='hs-conid'>One</span>  <span class='hs-layout'>(</span><span class='hs-varid'>x</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>40: </span>                      <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Many</span> <span class='hs-layout'>(</span><span class='hs-varid'>xs</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>ListNE</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>41: </span>                      <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Cons</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>           <span class='hs-layout'>(</span><span class='hs-varid'>xs</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>42: </span>                      <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Snoc</span> <span class='hs-layout'>(</span><span class='hs-varid'>xs</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>   <span class='hs-layout'>(</span><span class='hs-varid'>x</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>43: </span>                      <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Two</span>  <span class='hs-layout'>(</span><span class='hs-varid'>x</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>OrdListNE</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>y</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>OrdListNE</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>44: </span><span class='hs-keyword'>@-}</span>
</pre>
</div>

The OrdList Type
----------------

The `OrdList` type is defined as follows:


<pre><span class=hs-linenum>54: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>55: </span>  <span class='hs-keyglyph'>=</span> <span class='hs-conid'>None</span>
<span class=hs-linenum>56: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-conid'>One</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>57: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Many</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>        <span class='hs-comment'>-- Invariant: non-empty</span>
<span class=hs-linenum>58: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Cons</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>59: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Snoc</span> <span class='hs-layout'>(</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>60: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Two</span> <span class='hs-layout'>(</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-comment'>-- Invariant: non-empty</span>
<span class=hs-linenum>61: </span>        <span class='hs-layout'>(</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-comment'>-- Invariant: non-empty</span>
</pre>

As indicated by the comments the key invariants are that:

* `Many` should take a *non-empty* list,
* `Two` takes two non-empty `OrdList`s. 

What is a Non-Empty OrdList?
----------------------------

To proceed, we must tell LiquidHaskell what non-empty means. We do this
with a [measure][] that describes the *number of elements* in a structure.
When this number is strictly positive, the structure is non-empty.

 We've previously seen how to measure the size of a list.
<pre><span class=hs-linenum>77: </span><span class='hs-definition'>measure</span> <span class='hs-varid'>len</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>78: </span><span class='hs-definition'>len</span> <span class='hs-layout'>(</span><span class='hs-conid'>[]</span><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span>
<span class=hs-linenum>79: </span><span class='hs-definition'>len</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>
</pre>

We can use the same technique to measure the size of an `OrdList`.


<pre><span class=hs-linenum>85: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>olen</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>86: </span>    <span class='hs-varid'>olen</span> <span class='hs-layout'>(</span><span class='hs-conid'>None</span><span class='hs-layout'>)</span>      <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span>
<span class=hs-linenum>87: </span>    <span class='hs-varid'>olen</span> <span class='hs-layout'>(</span><span class='hs-conid'>One</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span>     <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span>
<span class=hs-linenum>88: </span>    <span class='hs-varid'>olen</span> <span class='hs-layout'>(</span><span class='hs-conid'>Many</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>89: </span>    <span class='hs-varid'>olen</span> <span class='hs-layout'>(</span><span class='hs-conid'>Cons</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>olen</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>90: </span>    <span class='hs-varid'>olen</span> <span class='hs-layout'>(</span><span class='hs-conid'>Snoc</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>olen</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>91: </span>    <span class='hs-varid'>olen</span> <span class='hs-layout'>(</span><span class='hs-conid'>Two</span> <span class='hs-varid'>x</span> <span class='hs-varid'>y</span><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>olen</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>olen</span> <span class='hs-varid'>y</span><span class='hs-layout'>)</span>
<span class=hs-linenum>92: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>93: </span>
<span class=hs-linenum>94: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>invariant</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>| (olen v) &gt;= 0}</span> <span class='hs-keyword'>@-}</span>
</pre>

Now, we can use the measures to define aliases for **non-empty** lists and `OrdList`s.


<pre><span class=hs-linenum>100: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>ListNE</span>    <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>       <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span>  <span class='hs-varop'>&gt;</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>101: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>OrdListNE</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>olen</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-varop'>&gt;</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

Capturing the Invariants In a Refined Type
------------------------------------------

Let's return to the original type, and refine it with the above non-empty
variants to specify the invariants as
 part of the data declaration
<pre><span class=hs-linenum>110: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>OrdList</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>olen</span><span class='hs-keyglyph'>]</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>111: </span>      <span class='hs-keyglyph'>=</span> <span class='hs-conid'>None</span>
<span class=hs-linenum>112: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-conid'>One</span>  <span class='hs-layout'>(</span><span class='hs-varid'>x</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>113: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Many</span> <span class='hs-layout'>(</span><span class='hs-varid'>xs</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>ListNE</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>114: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Cons</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>           <span class='hs-layout'>(</span><span class='hs-varid'>xs</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>115: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Snoc</span> <span class='hs-layout'>(</span><span class='hs-varid'>xs</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>   <span class='hs-layout'>(</span><span class='hs-varid'>x</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>116: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Two</span>  <span class='hs-layout'>(</span><span class='hs-varid'>x</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>OrdListNE</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>y</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>OrdListNE</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>117: </span>  <span class='hs-keyword'>@-}</span>
</pre>

Notice immediately that LiquidHaskell can use the refined definition to warn us 
about malformed `OrdList` values.


<pre><span class=hs-linenum>124: </span><a class=annot href="#"><span class=annottext>(OrdList.OrdList {VV : (GHC.Integer.Type.Integer) | (VV &gt; 0)})</span><span class='hs-definition'>ok</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x6 : [{x9 : (GHC.Integer.Type.Integer) | (x9 &gt; 0)}] | ((len x6) &gt; 0)}
-&gt; {x2 : (OrdList.OrdList {x9 : (GHC.Integer.Type.Integer) | (x9 &gt; 0)}) | ((olen x2) == (len x1))}</span><span class='hs-conid'>Many</span></a> <a class=annot href="#"><span class=annottext>{x5 : [{x11 : (GHC.Integer.Type.Integer) | (x11 &gt; 0)}]&lt;\x9 VV -&gt; (x8 &gt; 0) &amp;&amp; (x8 &gt; x9)&gt; | (((null x5)) &lt;=&gt; false) &amp;&amp; ((len x5) &gt;= 0) &amp;&amp; ((olens x5) &gt;= 0) &amp;&amp; ((sumLens x5) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><span class='hs-num'>1</span><span class='hs-layout'>,</span><span class='hs-num'>2</span><span class='hs-layout'>,</span><span class='hs-num'>3</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>125: </span><a class=annot href="#"><span class=annottext>forall a.
{VV : (OrdList.OrdList {VV : a | false}) | ((olen VV) == 0)}</span><span class='hs-definition'>bad</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x4 : [{VV : a | false}] | ((len x4) &gt; 0)}
-&gt; {x2 : (OrdList.OrdList {VV : a | false}) | ((olen x2) == (len x1))}</span><span class='hs-conid'>Many</span></a> <span class=hs-error><a class=annot href="#"><span class=annottext>{x8 : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (((null x8)) &lt;=&gt; true) &amp;&amp; ((len x8) == 0) &amp;&amp; ((olens x8) == 0) &amp;&amp; ((sumLens x8) == 0) &amp;&amp; ((len x8) &gt;= 0) &amp;&amp; ((olens x8) &gt;= 0) &amp;&amp; ((sumLens x8) &gt;= 0)}</span><span class='hs-conid'>[]</span></a></span>
<span class=hs-linenum>126: </span><a class=annot href="#"><span class=annottext>{VV : (OrdList.OrdList {VV : (GHC.Integer.Type.Integer) | (VV &gt; 0)}) | ((olen VV) == (olen OrdList.ok))}</span><span class='hs-definition'>badder</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x10 : (OrdList.OrdList {x12 : (GHC.Integer.Type.Integer) | (x12 &gt; 0)}) | ((olen x10) &gt; 0)}
-&gt; x2:{x6 : (OrdList.OrdList {x12 : (GHC.Integer.Type.Integer) | (x12 &gt; 0)}) | ((olen x6) &gt; 0)}
-&gt; {x2 : (OrdList.OrdList {x12 : (GHC.Integer.Type.Integer) | (x12 &gt; 0)}) | ((olen x2) == ((olen x1) + (olen x2)))}</span><span class='hs-conid'>Two</span></a> <span class=hs-error><a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList {x4 : (GHC.Integer.Type.Integer) | false}) | ((olen x3) == 0) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-conid'>None</span></a></span> <span class=hs-error><a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList {x5 : (GHC.Integer.Type.Integer) | (x5 &gt; 0)}) | (x3 == OrdList.ok) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>ok</span></a></span>
</pre>

All of the above are accepted by GHC, but only the first one is actually a valid
`OrdList`. Happily, LiquidHaskell will reject the latter two, as they violate
the invariants.


Basic Functions
---------------

Now let's look at some of the functions!

First, we'll define a handy alias for `OrdList`s of a given size:


<pre><span class=hs-linenum>142: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>OrdListN</span> <span class='hs-varid'>a</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>olen</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

Now, the `nilOL` constructor returns an empty `OrdList`:


<pre><span class=hs-linenum>148: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>nilOL</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>OrdListN</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>{0}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>149: </span><a class=annot href="#"><span class=annottext>forall a. {v : (OrdList.OrdList a) | ((olen v) == 0)}</span><span class='hs-definition'>nilOL</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a. {x2 : (OrdList.OrdList a) | ((olen x2) == 0)}</span><span class='hs-conid'>None</span></a>
</pre>

the `unitOL` constructor returns an `OrdList` with one element:


<pre><span class=hs-linenum>155: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>unitOL</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdListN</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>{1}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>156: </span><a class=annot href="#"><span class=annottext>forall a. a -&gt; {v : (OrdList.OrdList a) | ((olen v) == 1)}</span><span class='hs-definition'>unitOL</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-keyword'>as</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == as)}
-&gt; {x2 : (OrdList.OrdList {VV : a | (VV == as)}) | ((olen x2) == 1)}</span><span class='hs-conid'>One</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == as)}</span><span class='hs-keyword'>as</span></a>
</pre>

and `snocOL` and `consOL` return outputs with precisely one more element:


<pre><span class=hs-linenum>162: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>snocOL</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdListN</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>{1 + (olen xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>163: </span><a class=annot href="#"><span class=annottext>forall a.
xs:(OrdList.OrdList a)
-&gt; a -&gt; {v : (OrdList.OrdList a) | ((olen v) == (1 + (olen xs)))}</span><span class='hs-definition'>snocOL</span></a> <a class=annot href="#"><span class=annottext>(OrdList.OrdList a)</span><span class='hs-keyword'>as</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>b</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(OrdList.OrdList a)
-&gt; a -&gt; {x2 : (OrdList.OrdList a) | ((olen x2) == (1 + (olen x1)))}</span><span class='hs-conid'>Snoc</span></a> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == as) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-keyword'>as</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a>
<span class=hs-linenum>164: </span>
<span class=hs-linenum>165: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>consOL</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdListN</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>{1 + (olen xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>166: </span><a class=annot href="#"><span class=annottext>forall a.
a
-&gt; xs:(OrdList.OrdList a)
-&gt; {v : (OrdList.OrdList a) | ((olen v) == (1 + (olen xs)))}</span><span class='hs-definition'>consOL</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>(OrdList.OrdList a)</span><span class='hs-varid'>bs</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a
-&gt; x2:(OrdList.OrdList a)
-&gt; {x2 : (OrdList.OrdList a) | ((olen x2) == (1 + (olen x2)))}</span><span class='hs-conid'>Cons</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == bs) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>bs</span></a>
</pre>

**Note:** The `OrdListN a {e}` syntax just lets us use LiquidHaskell 
expressions `e` as a parameter to the type alias `OrdListN`.


<div class="hidden">

<pre><span class=hs-linenum>175: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>isNilOL</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Bool</span> <span class='hs-keyword'>| ((Prop v) &lt;=&gt; ((olen xs) = 0))}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>176: </span><a class=annot href="#"><span class=annottext>forall a.
xs:(OrdList.OrdList a)
-&gt; {v : (GHC.Types.Bool) | (((Prop v)) &lt;=&gt; ((olen xs) == 0))}</span><span class='hs-definition'>isNilOL</span></a> <span class='hs-conid'>None</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x3 : (GHC.Types.Bool) | ((Prop x3)) &amp;&amp; (x3 == GHC.Types.True)}</span><span class='hs-conid'>True</span></a>
<span class=hs-linenum>177: </span><span class='hs-definition'>isNilOL</span> <span class='hs-keyword'>_</span>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x3 : (GHC.Types.Bool) | (not (((Prop x3)))) &amp;&amp; (x3 == GHC.Types.False)}</span><span class='hs-conid'>False</span></a>
</pre>
</div>

Appending `OrdList`s
--------------------

The above functions really aren't terribly interesting, however, since their 
types fall right out of the definition of `olen`. 

So how about something that takes a little thinking?


<pre><span class=hs-linenum>190: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>appOL</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>191: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdListN</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>{(olen xs) + (olen ys)}</span>
<span class=hs-linenum>192: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>193: </span><span class='hs-conid'>None</span>  <a class=annot href="#"><span class=annottext>forall a.
xs:(OrdList.OrdList a)
-&gt; ys:(OrdList.OrdList a)
-&gt; {v : (OrdList.OrdList a) | ((olen v) == ((olen xs) + (olen ys)))}</span><span class='hs-varop'>`appOL`</span></a> <a class=annot href="#"><span class=annottext>(OrdList.OrdList a)</span><span class='hs-varid'>b</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == b) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>b</span></a>
<span class=hs-linenum>194: </span><span class='hs-definition'>a</span>     <span class='hs-varop'>`appOL`</span> <span class='hs-conid'>None</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : (OrdList.OrdList a) | ((olen x2) &gt;= 0)}</span><span class='hs-varid'>a</span></a>
<span class=hs-linenum>195: </span><span class='hs-conid'>One</span> <span class='hs-varid'>a</span> <span class='hs-varop'>`appOL`</span> <span class='hs-varid'>b</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == a) &amp;&amp; (VV &gt; a) &amp;&amp; (VV &lt; a)}
-&gt; x2:(OrdList.OrdList {VV : a | (VV == a) &amp;&amp; (VV &gt; a) &amp;&amp; (VV &lt; a)})
-&gt; {x2 : (OrdList.OrdList {VV : a | (VV == a) &amp;&amp; (VV &gt; a) &amp;&amp; (VV &lt; a)}) | ((olen x2) == (1 + (olen x2)))}</span><span class='hs-conid'>Cons</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == b) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>b</span></a>
<span class=hs-linenum>196: </span><span class='hs-definition'>a</span>     <span class='hs-varop'>`appOL`</span> <span class='hs-conid'>One</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(OrdList.OrdList {VV : a | (VV == b) &amp;&amp; (VV &gt; b) &amp;&amp; (VV &lt; b)})
-&gt; {VV : a | (VV == b) &amp;&amp; (VV &gt; b) &amp;&amp; (VV &lt; b)}
-&gt; {x2 : (OrdList.OrdList {VV : a | (VV == b) &amp;&amp; (VV &gt; b) &amp;&amp; (VV &lt; b)}) | ((olen x2) == (1 + (olen x1)))}</span><span class='hs-conid'>Snoc</span></a> <a class=annot href="#"><span class=annottext>{x2 : (OrdList.OrdList a) | ((olen x2) &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a>
<span class=hs-linenum>197: </span><span class='hs-definition'>a</span>     <span class='hs-varop'>`appOL`</span> <span class='hs-varid'>b</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x6 : (OrdList.OrdList a) | ((olen x6) &gt; 0)}
-&gt; x2:{x4 : (OrdList.OrdList a) | ((olen x4) &gt; 0)}
-&gt; {x2 : (OrdList.OrdList a) | ((olen x2) == ((olen x1) + (olen x2)))}</span><span class='hs-conid'>Two</span></a> <a class=annot href="#"><span class=annottext>{x2 : (OrdList.OrdList a) | ((olen x2) &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == b) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>b</span></a>
</pre>

`appOL` takes two `OrdList`s and returns a list whose length is the **sum of** 
the two input lists. The most important thing to notice here is that we haven't 
had to insert any extra checks in `appOL`, unlike the [GADT][] solution. 

LiquidHaskell uses the definition of `olen` to infer that in the last case of 
`appOL`, `a` and `b` *must be non-empty*, so they are valid arguments to `Two`.

We can prove other things about `OrdList`s as well, like the fact
that converting an `OrdList` to a Haskell list preserves length


<pre><span class=hs-linenum>211: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>toOL</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdListN</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>{(len xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>212: </span><a class=annot href="#"><span class=annottext>forall a.
xs:[a] -&gt; {v : (OrdList.OrdList a) | ((olen v) == (len xs))}</span><span class='hs-definition'>toOL</span></a> <span class='hs-conid'>[]</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a. {x2 : (OrdList.OrdList a) | ((olen x2) == 0)}</span><span class='hs-conid'>None</span></a>
<span class=hs-linenum>213: </span><span class='hs-definition'>toOL</span> <span class='hs-varid'>xs</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x4 : [a] | ((len x4) &gt; 0)}
-&gt; {x2 : (OrdList.OrdList a) | ((olen x2) == (len x1))}</span><span class='hs-conid'>Many</span></a> <a class=annot href="#"><span class=annottext>{x4 : [a] | ((len x4) &gt;= 0) &amp;&amp; ((olens x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

as does mapping over an `OrdList`


<pre><span class=hs-linenum>219: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>mapOL</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdListN</span> <span class='hs-varid'>b</span> <span class='hs-keyword'>{(olen xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>220: </span><a class=annot href="#"><span class=annottext>forall a b.
(b -&gt; a)
-&gt; x3:(OrdList.OrdList b)
-&gt; {VV : (OrdList.OrdList a) | ((olen VV) == (olen x3))}</span><span class='hs-definition'>mapOL</span></a> <span class='hs-keyword'>_</span> <span class='hs-conid'>None</span>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a. {x2 : (OrdList.OrdList a) | ((olen x2) == 0)}</span><span class='hs-conid'>None</span></a>
<span class=hs-linenum>221: </span><span class='hs-definition'>mapOL</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-conid'>One</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a -&gt; {x2 : (OrdList.OrdList a) | ((olen x2) == 1)}</span><span class='hs-conid'>One</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>222: </span><span class='hs-definition'>mapOL</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-conid'>Cons</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a
-&gt; x2:(OrdList.OrdList a)
-&gt; {x2 : (OrdList.OrdList a) | ((olen x2) == (1 + (olen x2)))}</span><span class='hs-conid'>Cons</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a b.
(b -&gt; a)
-&gt; x3:(OrdList.OrdList b)
-&gt; {VV : (OrdList.OrdList a) | ((olen VV) == (olen x3))}</span><span class='hs-varid'>mapOL</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == xs) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>223: </span><span class='hs-definition'>mapOL</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-conid'>Snoc</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(OrdList.OrdList a)
-&gt; a -&gt; {x2 : (OrdList.OrdList a) | ((olen x2) == (1 + (olen x1)))}</span><span class='hs-conid'>Snoc</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a b.
(b -&gt; a)
-&gt; x3:(OrdList.OrdList b)
-&gt; {VV : (OrdList.OrdList a) | ((olen VV) == (olen x3))}</span><span class='hs-varid'>mapOL</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == xs) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>224: </span><span class='hs-definition'>mapOL</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-conid'>Two</span> <span class='hs-varid'>x</span> <span class='hs-varid'>y</span><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x6 : (OrdList.OrdList a) | ((olen x6) &gt; 0)}
-&gt; x2:{x4 : (OrdList.OrdList a) | ((olen x4) &gt; 0)}
-&gt; {x2 : (OrdList.OrdList a) | ((olen x2) == ((olen x1) + (olen x2)))}</span><span class='hs-conid'>Two</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a b.
(b -&gt; a)
-&gt; x3:(OrdList.OrdList b)
-&gt; {VV : (OrdList.OrdList a) | ((olen VV) == (olen x3))}</span><span class='hs-varid'>mapOL</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x4 : (OrdList.OrdList a) | (x4 == x) &amp;&amp; ((olen x4) &gt; 0) &amp;&amp; ((olen x4) &gt;= 0)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a b.
(b -&gt; a)
-&gt; x3:(OrdList.OrdList b)
-&gt; {VV : (OrdList.OrdList a) | ((olen VV) == (olen x3))}</span><span class='hs-varid'>mapOL</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x4 : (OrdList.OrdList a) | (x4 == y) &amp;&amp; ((olen x4) &gt; 0) &amp;&amp; ((olen x4) &gt;= 0)}</span><span class='hs-varid'>y</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>225: </span><span class='hs-definition'>mapOL</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-conid'>Many</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x4 : [a] | ((len x4) &gt; 0)}
-&gt; {x2 : (OrdList.OrdList a) | ((olen x2) == (len x1))}</span><span class='hs-conid'>Many</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(a -&gt; b) -&gt; x3:[a] -&gt; {x2 : [b] | ((len x2) == (len x3))}</span><span class='hs-varid'>map</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x6 : [a] | (x6 == xs) &amp;&amp; ((len x6) &gt; 0) &amp;&amp; ((len x6) &gt;= 0) &amp;&amp; ((olens x6) &gt;= 0) &amp;&amp; ((sumLens x6) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
</pre>

as does converting a Haskell list to an `OrdList`.


<pre><span class=hs-linenum>231: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>ListN</span> <span class='hs-varid'>a</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>232: </span>
<span class=hs-linenum>233: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fromOL</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>ListN</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>{(olen xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>234: </span><a class=annot href="#"><span class=annottext>forall a.
xs:(OrdList.OrdList a) -&gt; {v : [a] | ((len v) == (olen xs))}</span><span class='hs-definition'>fromOL</span></a> <a class=annot href="#"><span class=annottext>(OrdList.OrdList a)</span><span class='hs-varid'>a</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(OrdList.OrdList a)
-&gt; x2:{x4 : [a] | ((len x4) == 0)}
-&gt; {x2 : [a] | ((len x2) == ((olen x1) + (len x2)))}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == a) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{x8 : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (((null x8)) &lt;=&gt; true) &amp;&amp; ((len x8) == 0) &amp;&amp; ((olens x8) == 0) &amp;&amp; ((sumLens x8) == 0) &amp;&amp; ((len x8) &gt;= 0) &amp;&amp; ((olens x8) &gt;= 0) &amp;&amp; ((sumLens x8) &gt;= 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>235: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>236: </span>    <span class='hs-keyword'>{-@</span> <span class='hs-varid'>go</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span>
<span class=hs-linenum>237: </span>           <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyword'>_</span> <span class='hs-keyword'>| (len v) = (olen xs) + (len ys)}</span>
<span class=hs-linenum>238: </span>      <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>239: </span>    <a class=annot href="#"><span class=annottext>x1:(OrdList.OrdList a)
-&gt; x2:{VV : [a] | ((len VV) &gt;= 0)}
-&gt; {v : [a] | ((len v) == ((olen x1) + (len x2)))}</span><span class='hs-varid'>go</span></a> <span class='hs-conid'>None</span>       <a class=annot href="#"><span class=annottext>{VV : [a] | ((len VV) &gt;= 0)}</span><span class='hs-varid'>acc</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x5 : [a] | (x5 == acc) &amp;&amp; ((len x5) &gt;= 0) &amp;&amp; ((olens x5) &gt;= 0) &amp;&amp; ((sumLens x5) &gt;= 0)}</span><span class='hs-varid'>acc</span></a>
<span class=hs-linenum>240: </span>    <span class='hs-varid'>go</span> <span class='hs-layout'>(</span><span class='hs-conid'>One</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>    <span class='hs-varid'>acc</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:a
-&gt; x2:[{VV : a&lt;p x1&gt; | true}]&lt;p&gt;
-&gt; {x5 : [a]&lt;p&gt; | (((null x5)) &lt;=&gt; false) &amp;&amp; ((len x5) == (1 + (len x2))) &amp;&amp; ((olens x5) == ((olen x1) + (olens x2))) &amp;&amp; ((sumLens x5) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{x5 : [a] | (x5 == acc) &amp;&amp; ((len x5) &gt;= 0) &amp;&amp; ((olens x5) &gt;= 0) &amp;&amp; ((sumLens x5) &gt;= 0)}</span><span class='hs-varid'>acc</span></a>
<span class=hs-linenum>241: </span>    <span class='hs-varid'>go</span> <span class='hs-layout'>(</span><span class='hs-conid'>Cons</span> <span class='hs-varid'>a</span> <span class='hs-varid'>b</span><span class='hs-layout'>)</span> <span class='hs-varid'>acc</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:a
-&gt; x2:[{VV : a&lt;p x1&gt; | true}]&lt;p&gt;
-&gt; {x5 : [a]&lt;p&gt; | (((null x5)) &lt;=&gt; false) &amp;&amp; ((len x5) == (1 + (len x2))) &amp;&amp; ((olens x5) == ((olen x1) + (olens x2))) &amp;&amp; ((sumLens x5) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>x1:(OrdList.OrdList a)
-&gt; x2:{VV : [a] | ((len VV) &gt;= 0)}
-&gt; {v : [a] | ((len v) == ((olen x1) + (len x2)))}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == b) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>{x5 : [a] | (x5 == acc) &amp;&amp; ((len x5) &gt;= 0) &amp;&amp; ((olens x5) &gt;= 0) &amp;&amp; ((sumLens x5) &gt;= 0)}</span><span class='hs-varid'>acc</span></a>
<span class=hs-linenum>242: </span>    <span class='hs-varid'>go</span> <span class='hs-layout'>(</span><span class='hs-conid'>Snoc</span> <span class='hs-varid'>a</span> <span class='hs-varid'>b</span><span class='hs-layout'>)</span> <span class='hs-varid'>acc</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(OrdList.OrdList a)
-&gt; x2:{VV : [a] | ((len VV) &gt;= 0)}
-&gt; {v : [a] | ((len v) == ((olen x1) + (len x2)))}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == a) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>a</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:a
-&gt; x2:[{VV : a&lt;p x1&gt; | true}]&lt;p&gt;
-&gt; {x5 : [a]&lt;p&gt; | (((null x5)) &lt;=&gt; false) &amp;&amp; ((len x5) == (1 + (len x2))) &amp;&amp; ((olens x5) == ((olen x1) + (olens x2))) &amp;&amp; ((sumLens x5) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{x5 : [a] | (x5 == acc) &amp;&amp; ((len x5) &gt;= 0) &amp;&amp; ((olens x5) &gt;= 0) &amp;&amp; ((sumLens x5) &gt;= 0)}</span><span class='hs-varid'>acc</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>243: </span>    <span class='hs-varid'>go</span> <span class='hs-layout'>(</span><span class='hs-conid'>Two</span> <span class='hs-varid'>a</span> <span class='hs-varid'>b</span><span class='hs-layout'>)</span>  <span class='hs-varid'>acc</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(OrdList.OrdList a)
-&gt; x2:{VV : [a] | ((len VV) &gt;= 0)}
-&gt; {v : [a] | ((len v) == ((olen x1) + (len x2)))}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{x4 : (OrdList.OrdList a) | (x4 == a) &amp;&amp; ((olen x4) &gt; 0) &amp;&amp; ((olen x4) &gt;= 0)}</span><span class='hs-varid'>a</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:(OrdList.OrdList a)
-&gt; x2:{VV : [a] | ((len VV) &gt;= 0)}
-&gt; {v : [a] | ((len v) == ((olen x1) + (len x2)))}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{x4 : (OrdList.OrdList a) | (x4 == b) &amp;&amp; ((olen x4) &gt; 0) &amp;&amp; ((olen x4) &gt;= 0)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>{x5 : [a] | (x5 == acc) &amp;&amp; ((len x5) &gt;= 0) &amp;&amp; ((olens x5) &gt;= 0) &amp;&amp; ((sumLens x5) &gt;= 0)}</span><span class='hs-varid'>acc</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>244: </span>    <span class='hs-varid'>go</span> <span class='hs-layout'>(</span><span class='hs-conid'>Many</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>  <span class='hs-varid'>acc</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x6 : [a] | (x6 == xs) &amp;&amp; ((len x6) &gt; 0) &amp;&amp; ((len x6) &gt;= 0) &amp;&amp; ((olens x6) &gt;= 0) &amp;&amp; ((sumLens x6) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>x1:[a]
-&gt; x2:[a] -&gt; {x2 : [a] | ((len x2) == ((len x1) + (len x2)))}</span><span class='hs-varop'>++</span></a> <a class=annot href="#"><span class=annottext>{x5 : [a] | (x5 == acc) &amp;&amp; ((len x5) &gt;= 0) &amp;&amp; ((olens x5) &gt;= 0) &amp;&amp; ((sumLens x5) &gt;= 0)}</span><span class='hs-varid'>acc</span></a>
</pre>

<div class="hidden">
though for this last one we actually need to provide an explicit
qualifier, which we haven't really seen so far. Can anyone guess why?


<pre><span class=hs-linenum>252: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>qualif</span> <span class='hs-conid'>Go</span><span class='hs-layout'>(</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span><span class='hs-layout'>,</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span><span class='hs-layout'>,</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span><span class='hs-conop'>:</span>
<span class=hs-linenum>253: </span>      <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>olen</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span>
<span class=hs-linenum>254: </span>  <span class='hs-keyword'>@-}</span>
</pre>

The answer is that the return type of `go` must refer to the length
of the `OrdList` that it's folding over *as well as* the length of
the accumulator `acc`! We haven't written a refinement like that in
any of our type signatures in this module, so LiquidHaskell doesn't
know to guess that type.
</div>

There's nothing super interesting to say about the `foldOL`s but I'll
include them here for completeness' sake.


<pre><span class=hs-linenum>268: </span><span class='hs-definition'>foldrOL</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>-&gt;</span><span class='hs-varid'>b</span><span class='hs-keyglyph'>-&gt;</span><span class='hs-varid'>b</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span>
<span class=hs-linenum>269: </span><a class=annot href="#"><span class=annottext>forall a b. (a -&gt; b -&gt; b) -&gt; b -&gt; (OrdList.OrdList a) -&gt; b</span><span class='hs-definition'>foldrOL</span></a> <span class='hs-keyword'>_</span> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>z</span></a> <span class='hs-conid'>None</span>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == z)}</span><span class='hs-varid'>z</span></a>
<span class=hs-linenum>270: </span><span class='hs-definition'>foldrOL</span> <span class='hs-varid'>k</span> <span class='hs-varid'>z</span> <span class='hs-layout'>(</span><span class='hs-conid'>One</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; b</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == z)}</span><span class='hs-varid'>z</span></a>
<span class=hs-linenum>271: </span><span class='hs-definition'>foldrOL</span> <span class='hs-varid'>k</span> <span class='hs-varid'>z</span> <span class='hs-layout'>(</span><span class='hs-conid'>Cons</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; b</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a b. (a -&gt; b -&gt; b) -&gt; b -&gt; (OrdList.OrdList a) -&gt; b</span><span class='hs-varid'>foldrOL</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; b</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == z)}</span><span class='hs-varid'>z</span></a> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == xs) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>272: </span><span class='hs-definition'>foldrOL</span> <span class='hs-varid'>k</span> <span class='hs-varid'>z</span> <span class='hs-layout'>(</span><span class='hs-conid'>Snoc</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b. (a -&gt; b -&gt; b) -&gt; b -&gt; (OrdList.OrdList a) -&gt; b</span><span class='hs-varid'>foldrOL</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; b</span><span class='hs-varid'>k</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>a -&gt; b -&gt; b</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == z)}</span><span class='hs-varid'>z</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == xs) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>273: </span><span class='hs-definition'>foldrOL</span> <span class='hs-varid'>k</span> <span class='hs-varid'>z</span> <span class='hs-layout'>(</span><span class='hs-conid'>Two</span> <span class='hs-varid'>b1</span> <span class='hs-varid'>b2</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b. (a -&gt; b -&gt; b) -&gt; b -&gt; (OrdList.OrdList a) -&gt; b</span><span class='hs-varid'>foldrOL</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; b</span><span class='hs-varid'>k</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a b. (a -&gt; b -&gt; b) -&gt; b -&gt; (OrdList.OrdList a) -&gt; b</span><span class='hs-varid'>foldrOL</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; b</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == z)}</span><span class='hs-varid'>z</span></a> <a class=annot href="#"><span class=annottext>{x4 : (OrdList.OrdList a) | (x4 == b2) &amp;&amp; ((olen x4) &gt; 0) &amp;&amp; ((olen x4) &gt;= 0)}</span><span class='hs-varid'>b2</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x4 : (OrdList.OrdList a) | (x4 == b1) &amp;&amp; ((olen x4) &gt; 0) &amp;&amp; ((olen x4) &gt;= 0)}</span><span class='hs-varid'>b1</span></a>
<span class=hs-linenum>274: </span><span class='hs-definition'>foldrOL</span> <span class='hs-varid'>k</span> <span class='hs-varid'>z</span> <span class='hs-layout'>(</span><span class='hs-conid'>Many</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(a -&gt; b -&gt; b) -&gt; b -&gt; [a] -&gt; b</span><span class='hs-varid'>foldr</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; b</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == z)}</span><span class='hs-varid'>z</span></a> <a class=annot href="#"><span class=annottext>{x6 : [a] | (x6 == xs) &amp;&amp; ((len x6) &gt; 0) &amp;&amp; ((len x6) &gt;= 0) &amp;&amp; ((olens x6) &gt;= 0) &amp;&amp; ((sumLens x6) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>275: </span>
<span class=hs-linenum>276: </span><span class='hs-definition'>foldlOL</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>b</span><span class='hs-keyglyph'>-&gt;</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>-&gt;</span><span class='hs-varid'>b</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span>
<span class=hs-linenum>277: </span><a class=annot href="#"><span class=annottext>forall a b. (a -&gt; b -&gt; a) -&gt; a -&gt; (OrdList.OrdList b) -&gt; a</span><span class='hs-definition'>foldlOL</span></a> <span class='hs-keyword'>_</span> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>z</span></a> <span class='hs-conid'>None</span>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == z)}</span><span class='hs-varid'>z</span></a>
<span class=hs-linenum>278: </span><span class='hs-definition'>foldlOL</span> <span class='hs-varid'>k</span> <span class='hs-varid'>z</span> <span class='hs-layout'>(</span><span class='hs-conid'>One</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; a</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == z)}</span><span class='hs-varid'>z</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>279: </span><span class='hs-definition'>foldlOL</span> <span class='hs-varid'>k</span> <span class='hs-varid'>z</span> <span class='hs-layout'>(</span><span class='hs-conid'>Cons</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b. (a -&gt; b -&gt; a) -&gt; a -&gt; (OrdList.OrdList b) -&gt; a</span><span class='hs-varid'>foldlOL</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; a</span><span class='hs-varid'>k</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>a -&gt; b -&gt; a</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == z)}</span><span class='hs-varid'>z</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == xs) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>280: </span><span class='hs-definition'>foldlOL</span> <span class='hs-varid'>k</span> <span class='hs-varid'>z</span> <span class='hs-layout'>(</span><span class='hs-conid'>Snoc</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; a</span><span class='hs-varid'>k</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a b. (a -&gt; b -&gt; a) -&gt; a -&gt; (OrdList.OrdList b) -&gt; a</span><span class='hs-varid'>foldlOL</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; a</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == z)}</span><span class='hs-varid'>z</span></a> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == xs) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>281: </span><span class='hs-definition'>foldlOL</span> <span class='hs-varid'>k</span> <span class='hs-varid'>z</span> <span class='hs-layout'>(</span><span class='hs-conid'>Two</span> <span class='hs-varid'>b1</span> <span class='hs-varid'>b2</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b. (a -&gt; b -&gt; a) -&gt; a -&gt; (OrdList.OrdList b) -&gt; a</span><span class='hs-varid'>foldlOL</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; a</span><span class='hs-varid'>k</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a b. (a -&gt; b -&gt; a) -&gt; a -&gt; (OrdList.OrdList b) -&gt; a</span><span class='hs-varid'>foldlOL</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; a</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == z)}</span><span class='hs-varid'>z</span></a> <a class=annot href="#"><span class=annottext>{x4 : (OrdList.OrdList a) | (x4 == b1) &amp;&amp; ((olen x4) &gt; 0) &amp;&amp; ((olen x4) &gt;= 0)}</span><span class='hs-varid'>b1</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x4 : (OrdList.OrdList a) | (x4 == b2) &amp;&amp; ((olen x4) &gt; 0) &amp;&amp; ((olen x4) &gt;= 0)}</span><span class='hs-varid'>b2</span></a>
<span class=hs-linenum>282: </span><span class='hs-definition'>foldlOL</span> <span class='hs-varid'>k</span> <span class='hs-varid'>z</span> <span class='hs-layout'>(</span><span class='hs-conid'>Many</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(a -&gt; b -&gt; a) -&gt; a -&gt; [b] -&gt; a</span><span class='hs-varid'>foldl</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; a</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == z)}</span><span class='hs-varid'>z</span></a> <a class=annot href="#"><span class=annottext>{x6 : [a] | (x6 == xs) &amp;&amp; ((len x6) &gt; 0) &amp;&amp; ((len x6) &gt;= 0) &amp;&amp; ((olens x6) &gt;= 0) &amp;&amp; ((sumLens x6) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>


Concatenatation: Nested Measures
--------------------------------

Now, the astute readers will have probably noticed that I'm missing 
one function, `concatOL`, which glues a list of `OrdList`s into a 
single long `OrdList`.

With LiquidHaskell we can give `concatOL` a super precise type, which 
states that the size of the output list equals the *sum-of-the-sizes* 
of the input `OrdLists`.


<pre><span class=hs-linenum>298: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>concatOL</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdListN</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>{(olens xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>299: </span><a class=annot href="#"><span class=annottext>forall a.
x1:[(OrdList.OrdList a)]
-&gt; {VV : (OrdList.OrdList a) | ((olen VV) == (olens x1))}</span><span class='hs-definition'>concatOL</span></a> <span class='hs-conid'>[]</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a. {x2 : (OrdList.OrdList a) | ((olen x2) == 0)}</span><span class='hs-conid'>None</span></a>
<span class=hs-linenum>300: </span><span class='hs-definition'>concatOL</span> <span class='hs-layout'>(</span><span class='hs-varid'>ol</span><span class='hs-conop'>:</span><span class='hs-varid'>ols</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList a) | (x3 == ol) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-varid'>ol</span></a> <a class=annot href="#"><span class=annottext>x1:(OrdList.OrdList a)
-&gt; x2:(OrdList.OrdList a)
-&gt; {x2 : (OrdList.OrdList a) | ((olen x2) == ((olen x1) + (olen x2)))}</span><span class='hs-varop'>`appOL`</span></a> <a class=annot href="#"><span class=annottext>forall a.
x1:[(OrdList.OrdList a)]
-&gt; {VV : (OrdList.OrdList a) | ((olen VV) == (olens x1))}</span><span class='hs-varid'>concatOL</span></a> <a class=annot href="#"><span class=annottext>{x5 : [(OrdList.OrdList a)] | (x5 == ols) &amp;&amp; ((len x5) &gt;= 0) &amp;&amp; ((olens x5) &gt;= 0) &amp;&amp; ((sumLens x5) &gt;= 0)}</span><span class='hs-varid'>ols</span></a>
</pre>

The notion of *sum-of-the-sizes* of the input lists is specifed by the measure


<pre><span class=hs-linenum>306: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>olens</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>307: </span>    <span class='hs-varid'>olens</span> <span class='hs-layout'>(</span><span class='hs-conid'>[]</span><span class='hs-layout'>)</span>     <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span>
<span class=hs-linenum>308: </span>    <span class='hs-varid'>olens</span> <span class='hs-layout'>(</span><span class='hs-varid'>ol</span><span class='hs-conop'>:</span><span class='hs-varid'>ols</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>olen</span> <span class='hs-varid'>ol</span><span class='hs-layout'>)</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>olens</span> <span class='hs-varid'>ols</span><span class='hs-layout'>)</span>
<span class=hs-linenum>309: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>310: </span>
<span class=hs-linenum>311: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>invariant</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>OrdList</span> <span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (olens v) &gt;= 0}</span> <span class='hs-keyword'>@-}</span>
</pre>

LiquidHaskell is happy to verify the above signature, again without 
requiring any explict proofs. 

Conclusion
----------

The above illustrates the flexibility provided by LiquidHaskell *measures*.

Instead of having to bake particular invariants into a datatype using indices
or phantom types (as in the [GADT][] approach), we are able to split our 
properties out into independent *views* of the datatype, yielding an approach
that is more modular as 

* we didn't have to go back and change the definition of `[]` to talk about `OrdList`s,
* we didn't have to provide explict non-emptiness witnesses,
* we obtained extra information about the behavior of API functions like `concatOL`.


<div class="hidden">
We can actually even verify the original definition of `concatOL` with a
clever use of *abstract refinements*, but we have to slightly change
the signature of `foldr`.


<pre><span class=hs-linenum>338: </span><span class='hs-comment'>{- UGH CAN'T PARSE `GHC.Types.:`...
foldr' :: forall &lt;p :: [a] -&gt; b -&gt; Prop&gt;.
          (xs:[a] -&gt; x:a -&gt; b&lt;p xs&gt; -&gt; b&lt;p (GHC.Types.: x xs)&gt;)
       -&gt; b&lt;p GHC.Types.[]&gt;
       -&gt; ys:[a]
       -&gt; b&lt;p ys&gt;
@-}</span>
<span class=hs-linenum>345: </span><a class=annot href="#"><span class=annottext>forall a b.
({VV : [a] | ((len VV) &gt;= 0)} -&gt; a -&gt; b -&gt; b) -&gt; b -&gt; [a] -&gt; b</span><span class='hs-definition'>foldr'</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | ((len VV) &gt;= 0)} -&gt; a -&gt; b -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>z</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == z)}</span><span class='hs-varid'>z</span></a>
<span class=hs-linenum>346: </span><span class='hs-definition'>foldr'</span> <span class='hs-varid'>f</span> <span class='hs-varid'>z</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : [a] | ((len x2) &gt;= 0)} -&gt; a -&gt; b -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x5 : [a] | (x5 == xs) &amp;&amp; ((len x5) &gt;= 0) &amp;&amp; ((olens x5) &gt;= 0) &amp;&amp; ((sumLens x5) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a b.
({VV : [a] | ((len VV) &gt;= 0)} -&gt; a -&gt; b -&gt; b) -&gt; b -&gt; [a] -&gt; b</span><span class='hs-varid'>foldr'</span></a> <a class=annot href="#"><span class=annottext>{x2 : [a] | ((len x2) &gt;= 0)} -&gt; a -&gt; b -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == z)}</span><span class='hs-varid'>z</span></a> <a class=annot href="#"><span class=annottext>{x5 : [a] | (x5 == xs) &amp;&amp; ((len x5) &gt;= 0) &amp;&amp; ((olens x5) &gt;= 0) &amp;&amp; ((sumLens x5) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
</pre>

We've added a *ghost parameter* to the folding function, letting us
refer to the tail of the list at each folding step. This lets us
encode inductive reasoning in the type of `foldr`, specifically that

1. given a base case `z` that satisfies `p []`
2. and a function that, given a value that satisfies `p xs`, returns
a value satisfying `p (x:xs)`
3. the value returned by `foldr f z ys` must satisfy `p ys`!

LiquidHaskell can use this signature, instantiating `p` with `\xs
-> {v:OrdList a | (olen v) = (olens xs)}` to prove the original
definition of `concatOL`!


<pre><span class=hs-linenum>363: </span><span class='hs-comment'>{- concatOL' :: xs:[OrdList a] -&gt; OrdListN a {(olens xs)} @-}</span>
<span class=hs-linenum>364: </span><a class=annot href="#"><span class=annottext>forall a. [(OrdList.OrdList a)] -&gt; (OrdList.OrdList a)</span><span class='hs-definition'>concatOL'</span></a> <a class=annot href="#"><span class=annottext>[(OrdList.OrdList a)]</span><span class='hs-varid'>aas</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>([(OrdList.OrdList a)]
 -&gt; (OrdList.OrdList a)
 -&gt; (OrdList.OrdList a)
 -&gt; (OrdList.OrdList a))
-&gt; (OrdList.OrdList a)
-&gt; [(OrdList.OrdList a)]
-&gt; (OrdList.OrdList a)</span><span class='hs-varid'>foldr'</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(x5:(OrdList.OrdList a)
 -&gt; x6:(OrdList.OrdList a)
 -&gt; {x15 : (OrdList.OrdList a) | ((olen x15) == ((olen x5) + (olen x6))) &amp;&amp; ((olen x15) == ((olen x6) + (olen x5)))})
-&gt; [(OrdList.OrdList a)]
-&gt; x5:(OrdList.OrdList a)
-&gt; x6:(OrdList.OrdList a)
-&gt; {x15 : (OrdList.OrdList a) | ((olen x15) == ((olen x5) + (olen x6))) &amp;&amp; ((olen x15) == ((olen x6) + (olen x5)))}</span><span class='hs-varid'>const</span></a> <a class=annot href="#"><span class=annottext>x1:(OrdList.OrdList a)
-&gt; x2:(OrdList.OrdList a)
-&gt; {x2 : (OrdList.OrdList a) | ((olen x2) == ((olen x1) + (olen x2)))}</span><span class='hs-varid'>appOL</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x3 : (OrdList.OrdList {VV : a | false}) | ((olen x3) == 0) &amp;&amp; ((olen x3) &gt;= 0)}</span><span class='hs-conid'>None</span></a> <a class=annot href="#"><span class=annottext>{x5 : [(OrdList.OrdList a)] | (x5 == aas) &amp;&amp; ((len x5) &gt;= 0) &amp;&amp; ((olens x5) &gt;= 0) &amp;&amp; ((sumLens x5) &gt;= 0)}</span><span class='hs-varid'>aas</span></a>
</pre>

We haven't added the modified version of `foldr` to the LiquidHaskell
Prelude yet because it adds the ghost variable to the Haskell
type-signature.
</div>

[GADT]: http://www.reddit.com/r/haskell/comments/1xiurm/how_to_define_append_for_ordlist_defined_as_gadt/cfbrinr
[Reddit]: http://www.reddit.com/r/haskell/comments/1xiurm/how_to_define_append_for_ordlist_defined_as_gadt/
[OrdList]: http://www.haskell.org/platform/doc/2013.2.0.0/ghc-api/OrdList.html
[measure]: http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/
