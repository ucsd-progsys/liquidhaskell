---
layout: post
title: Polymorphic Perplexion
date: 2020-04-12
comments: true
author: Ranjit Jhala 
published: true
tags:
   - basic
demo: Insert.hs
---

Polymorphism plays a vital role in automating verification in LH.
However, thanks to its ubiquity, we often take it for granted, and 
it can be quite baffling to figure out why verification fails with 
monomorphic signatures. Let me explain why, using a simple example 
that has puzzled me and other users several times.

<!-- more -->

<div class="hidden">

<pre><span class=hs-linenum>22: </span>
<span class=hs-linenum>23: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>PolymorphicPerplexion</span> <span class='hs-keyword'>where</span>
</pre>
</div>

A Type for Ordered Lists
------------------------

[Previously](2013-07-29-putting-things-in-order.lhs.md)
we have seen how you can use LH to define a type of lists whose values are in increasing
(ok, non-decreasing!) order.

First, we define an `IncList a` type, with `Emp` ("empty") 
and `:<` ("cons") constructors.


<pre><span class=hs-linenum>38: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>IncList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Emp</span>
<span class=hs-linenum>39: </span>               <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conop'>:&lt;</span><span class='hs-layout'>)</span> <span class='hs-layout'>{</span> <span class='hs-varid'>hd</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>,</span> <span class='hs-varid'>tl</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>IncList</span> <span class='hs-varid'>a</span> <span class='hs-layout'>}</span>
<span class=hs-linenum>40: </span>
<span class=hs-linenum>41: </span><span class='hs-keyword'>infixr</span> <span class='hs-num'>9</span> <span class='hs-conop'>:&lt;</span>
</pre>

Next, we refine the type to specify that each "cons" `:<`
constructor takes as input a `hd` and a `tl` which must 
be an `IncList a` of values `v` each of which is greater 
than `hd`. 


<pre><span class=hs-linenum>50: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>IncList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Emp</span> 
<span class=hs-linenum>51: </span>                   <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conop'>:&lt;</span><span class='hs-layout'>)</span> <span class='hs-layout'>{</span> <span class='hs-varid'>hd</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>,</span> <span class='hs-varid'>tl</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>IncList</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>hd</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span><span class='hs-layout'>}</span>  
<span class=hs-linenum>52: </span>  <span class='hs-keyword'>@-}</span>
</pre>

We can confirm that the above definition ensures that the only 
*legal* values are increasingly ordered lists, as LH accepts
the first list below, but rejects the second where the elements
are out of order.


<pre><span class=hs-linenum>61: </span><span class='hs-definition'>legalList</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>IncList</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>62: </span><a class=annot href="#"><span class=annottext>(PolymorphicPerplexion.IncList GHC.Types.Int)</span><span class='hs-definition'>legalList</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-num'>0</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-num'>1</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-num'>2</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-num'>3</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>{VV : forall a . (PolymorphicPerplexion.IncList a) | VV == Emp}</span><span class='hs-conid'>Emp</span></a>
<span class=hs-linenum>63: </span>
<span class=hs-linenum>64: </span><span class='hs-definition'>illegalList</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>IncList</span> <span class='hs-conid'>Int</span> 
<span class=hs-linenum>65: </span><a class=annot href="#"><span class=annottext>(PolymorphicPerplexion.IncList GHC.Types.Int)</span><span class='hs-definition'>illegalList</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-num'>0</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-num'>1</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-num'>3</span></a> <span class='hs-conop'>:&lt;</span> <span class=hs-error><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-num'>2</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-conop'>:&lt;</span></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{VV : forall a . (PolymorphicPerplexion.IncList a) | VV == Emp}</span><span class='hs-conid'>Emp</span></a></span>
</pre>

A Polymorphic Insertion Sort
----------------------------

Next, lets write a simple *insertion-sort* function that 
takes a plain unordered list of `[a]` and returns the elements 
in increasing order:


<pre><span class=hs-linenum>76: </span><span class='hs-definition'>insertSortP</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncList</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>77: </span><a class=annot href="#"><span class=annottext>forall a .
(GHC.Classes.Ord&lt;[]&gt; a) =&gt;
[a] -&gt; (PolymorphicPerplexion.IncList a)</span><span class='hs-definition'>insertSortP</span></a> <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>xs</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>foldr</span> <a class=annot href="#"><span class=annottext>a -&gt; (PolymorphicPerplexion.IncList a) -&gt; (PolymorphicPerplexion.IncList a)</span><span class='hs-varid'>insertP</span></a> <a class=annot href="#"><span class=annottext>{VV : forall a . (PolymorphicPerplexion.IncList a) | VV == Emp}</span><span class='hs-conid'>Emp</span></a> <a class=annot href="#"><span class=annottext>{v : [a] | len v &gt;= 0
           &amp;&amp; v == xs}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>78: </span>
<span class=hs-linenum>79: </span><span class='hs-definition'>insertP</span>             <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncList</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>80: </span><a class=annot href="#"><span class=annottext>forall a .
(GHC.Classes.Ord&lt;[]&gt; a) =&gt;
a -&gt; (PolymorphicPerplexion.IncList a) -&gt; (PolymorphicPerplexion.IncList a)</span><span class='hs-definition'>insertP</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>y</span></a> <span class='hs-conid'>Emp</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | VV == y}</span><span class='hs-varid'>y</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>{VV : forall a . (PolymorphicPerplexion.IncList a) | VV == Emp}</span><span class='hs-conid'>Emp</span></a>
<span class=hs-linenum>81: </span><span class='hs-definition'>insertP</span> <span class='hs-varid'>y</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-conop'>:&lt;</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>82: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | VV == y}</span><span class='hs-varid'>y</span></a> <span class='hs-varop'>&lt;=</span> <a class=annot href="#"><span class=annottext>{VV : a | VV == x}</span><span class='hs-varid'>x</span></a>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | VV == y}</span><span class='hs-varid'>y</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>{VV : a | VV == x}</span><span class='hs-varid'>x</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>{v : (PolymorphicPerplexion.IncList {VV : a | x &lt;= VV}) | v == xs}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>83: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | VV == x}</span><span class='hs-varid'>x</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>(PolymorphicPerplexion.IncList a)</span><span class='hs-varid'>insertP</span></a> <a class=annot href="#"><span class=annottext>{VV : a | VV == y}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>{v : (PolymorphicPerplexion.IncList {VV : a | x &lt;= VV}) | v == xs}</span><span class='hs-varid'>xs</span></a>
</pre>

Happily, LH is able to verify the above code without any trouble!
(If that seemed too easy, don't worry: if you mess up the comparison, 
e.g. change the guard to `x <= y` LH will complain about it.)


A Monomorphic Insertion Sort
----------------------------

However, lets take the *exact* same code as above *but* change 
the type signatures to make the functions *monomorphic*, here, 
specialized to `Int` lists.


<pre><span class=hs-linenum>99: </span><span class='hs-definition'>insertSortM</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncList</span> <span class='hs-conid'>Int</span> 
<span class=hs-linenum>100: </span><a class=annot href="#"><span class=annottext>[GHC.Types.Int] -&gt; (PolymorphicPerplexion.IncList GHC.Types.Int)</span><span class='hs-definition'>insertSortM</span></a> <a class=annot href="#"><span class=annottext>[GHC.Types.Int]</span><span class='hs-varid'>xs</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>foldr</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; (PolymorphicPerplexion.IncList GHC.Types.Int) -&gt; (PolymorphicPerplexion.IncList GHC.Types.Int)</span><span class='hs-varid'>insertM</span></a> <a class=annot href="#"><span class=annottext>{VV : forall a . (PolymorphicPerplexion.IncList a) | VV == Emp}</span><span class='hs-conid'>Emp</span></a> <a class=annot href="#"><span class=annottext>{v : [GHC.Types.Int] | len v &gt;= 0
                       &amp;&amp; v == xs}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>101: </span>
<span class=hs-linenum>102: </span><span class='hs-definition'>insertM</span>            <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncList</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncList</span> <span class='hs-conid'>Int</span> 
<span class=hs-linenum>103: </span><a class=annot href="#"><span class=annottext>GHC.Types.Int -&gt; (PolymorphicPerplexion.IncList GHC.Types.Int) -&gt; (PolymorphicPerplexion.IncList GHC.Types.Int)</span><span class='hs-definition'>insertM</span></a> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>y</span></a> <span class='hs-conid'>Emp</span>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == y}</span><span class='hs-varid'>y</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>{VV : forall a . (PolymorphicPerplexion.IncList a) | VV == Emp}</span><span class='hs-conid'>Emp</span></a>
<span class=hs-linenum>104: </span><span class='hs-definition'>insertM</span> <span class='hs-varid'>y</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-conop'>:&lt;</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>105: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == y}</span><span class='hs-varid'>y</span></a> <span class='hs-varop'>&lt;=</span> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == x}</span><span class='hs-varid'>x</span></a>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == y}</span><span class='hs-varid'>y</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == x}</span><span class='hs-varid'>x</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>{v : (PolymorphicPerplexion.IncList {v : GHC.Types.Int | x &lt;= v}) | v == xs}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>106: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == x}</span><span class='hs-varid'>x</span></a> <span class='hs-conop'>:&lt;</span> <span class=hs-error><a class=annot href="#"><span class=annottext>(PolymorphicPerplexion.IncList GHC.Types.Int)</span><span class='hs-varid'>insertM</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == y}</span><span class='hs-varid'>y</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{v : (PolymorphicPerplexion.IncList {v : GHC.Types.Int | x &lt;= v}) | v == xs}</span><span class='hs-varid'>xs</span></a></span>
</pre>

Huh? Now LH appears to be unhappy with the code! How is this possible?

Lets look at the type error:


<pre><span class=hs-linenum>114: </span> <span class='hs-varop'>/</span><span class='hs-conid'>Users</span><span class='hs-varop'>/</span><span class='hs-varid'>rjhala</span><span class='hs-varop'>/</span><span class='hs-conid'>PerplexingPolymorphicProperties.lhs</span><span class='hs-conop'>:</span><span class='hs-num'>80</span><span class='hs-conop'>:</span><span class='hs-num'>27</span><span class='hs-comment'>-</span><span class='hs-num'>38</span><span class='hs-conop'>:</span> <span class='hs-conid'>Error</span><span class='hs-conop'>:</span> <span class='hs-conid'>Liquid</span> <span class='hs-conid'>Type</span> <span class='hs-conid'>Mismatch</span>
<span class=hs-linenum>115: </span>  
<span class=hs-linenum>116: </span> <span class='hs-num'>80</span> <span class='hs-keyglyph'>|</span>   <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>      <span class='hs-keyglyph'>=</span> <span class='hs-varid'>x</span> <span class='hs-conop'>:&lt;</span> <span class='hs-varid'>insertM</span> <span class='hs-varid'>y</span> <span class='hs-varid'>xs</span>
<span class=hs-linenum>117: </span>                                <span class='hs-varop'>^^^^^^^^^^^^</span>
<span class=hs-linenum>118: </span>   <span class='hs-conid'>Inferred</span> <span class='hs-keyword'>type</span>
<span class=hs-linenum>119: </span>     <span class='hs-conid'>VV</span> <span class='hs-conop'>:</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>120: </span>  
<span class=hs-linenum>121: </span>   <span class='hs-varid'>not</span> <span class='hs-varid'>a</span> <span class='hs-varid'>subtype</span> <span class='hs-keyword'>of</span> <span class='hs-conid'>Required</span> <span class='hs-keyword'>type</span>
<span class=hs-linenum>122: </span>     <span class='hs-conid'>VV</span> <span class='hs-conop'>:</span> <span class='hs-layout'>{</span><span class='hs-conid'>VV</span> <span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>x</span> <span class='hs-varop'>&lt;=</span> <span class='hs-conid'>VV</span><span class='hs-layout'>}</span>
<span class=hs-linenum>123: </span>  
<span class=hs-linenum>124: </span>   <span class='hs-conid'>In</span> <span class='hs-conid'>Context</span>
<span class=hs-linenum>125: </span>     <span class='hs-varid'>x</span> <span class='hs-conop'>:</span> <span class='hs-conid'>Int</span>
</pre>

LH *expects* that since we're using the "cons" operator `:<` the "tail"
value `insertM y xs` must contain values `VV` that are greater than the 
"head" `x`. The error says that, LH cannot prove this requirement of 
*actual* list `insertM y xs`.

Hmm, well thats a puzzler. Two questions that should come to mind.

1. *Why* does the above fact hold in the first place? 

2. *How* is LH able to deduce this fact with the *polymorphic* signature but not the monomorphic one?

Lets ponder the first question: why *is* every element 
of `insert y xs` in fact larger than `x`? For three reasons:

(a) every element in `xs` is larger than `x`, as the 
    list `x :< xs` was ordered, 

(b) `y` is larger than `x` as established by the `otherwise` and crucially

(c) the elements returned by `insert y xs` are either `y` or from `xs`!

Now onto the second question: how *does* LH verify the polymorphic code,
but not the monomorphic one? The reason is the fact (c)! LH is a *modular*
verifier, meaning that the *only* information that it has about the behavior
of `insert` at a call-site is the information captured in the (refinement) 
*type specification* for `insert`. The *polymorphic* signature:


<pre><span class=hs-linenum>156: </span><span class='hs-definition'>insertP</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncList</span> <span class='hs-varid'>a</span>
</pre>

via *parametricity*, implicitly states fact (c). That is, if at a call-site 
`insertP y xs` we pass in a value that is greater an `x` and a list of values 
greater than `x` then via *polymorphic instantiation* at the call-site, LH 
infers that the returned value must also be a list of elements greater than `x`!

However, the *monomorphic* signature 


<pre><span class=hs-linenum>167: </span><span class='hs-definition'>insertM</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncList</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncList</span> <span class='hs-conid'>Int</span> 
</pre>

offers no such insight. It simply says the function takes in an `Int` and another 
ordered list of `Int` and returns another ordered list, whose actual elements could 
be arbitrary `Int`. Specifically, at the call-site `insertP y xs` LH has no way to 
conclude the the returned elements are indeed greater than `x` and hence rejects 
the monomorphic code.


Perplexity
----------

While parametricity is all very nice, and LH's polymorphic instanatiation is very 
clever and useful, it can also be quite mysterious. For example, q curious user 
Oisín [pointed out](https://github.com/ucsd-progsys/liquidhaskell-tutorial/issues/91) 
that while the code below is *rejected* that if you *uncomment* the type signature 
for `go` then it is *accepted* by LH!


<pre><span class=hs-linenum>187: </span><span class='hs-definition'>insertSortP'</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncList</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>188: </span><a class=annot href="#"><span class=annottext>forall a .
(GHC.Classes.Ord&lt;[]&gt; a) =&gt;
[a] -&gt; (PolymorphicPerplexion.IncList a)</span><span class='hs-definition'>insertSortP'</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(PolymorphicPerplexion.IncList a)</span><span class='hs-varid'>foldr</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (PolymorphicPerplexion.IncList a) -&gt; (PolymorphicPerplexion.IncList a)</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : forall a . (PolymorphicPerplexion.IncList a) | VV == Emp}</span><span class='hs-conid'>Emp</span></a> 
<span class=hs-linenum>189: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>190: </span>    <span class='hs-comment'>-- go :: (Ord a) =&gt; a -&gt; IncList a -&gt; IncList a</span>
<span class=hs-linenum>191: </span>    <a class=annot href="#"><span class=annottext>a -&gt; (PolymorphicPerplexion.IncList a) -&gt; (PolymorphicPerplexion.IncList a)</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>y</span></a> <span class='hs-conid'>Emp</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | VV == y}</span><span class='hs-varid'>y</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>{VV : forall a . (PolymorphicPerplexion.IncList a) | VV == Emp}</span><span class='hs-conid'>Emp</span></a>
<span class=hs-linenum>192: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>y</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-conop'>:&lt;</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>193: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | VV == y}</span><span class='hs-varid'>y</span></a> <span class='hs-varop'>&lt;=</span> <a class=annot href="#"><span class=annottext>{VV : a | VV == x}</span><span class='hs-varid'>x</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | VV == y}</span><span class='hs-varid'>y</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>{VV : a | VV == x}</span><span class='hs-varid'>x</span></a> <span class='hs-conop'>:&lt;</span> <a class=annot href="#"><span class=annottext>{v : (PolymorphicPerplexion.IncList {VV : a | x &lt;= VV}) | v == xs}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>194: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | VV == x}</span><span class='hs-varid'>x</span></a> <span class='hs-conop'>:&lt;</span> <span class=hs-error><a class=annot href="#"><span class=annottext>(PolymorphicPerplexion.IncList a)</span><span class='hs-varid'>go</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{VV : a | VV == y}</span><span class='hs-varid'>y</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{v : (PolymorphicPerplexion.IncList {VV : a | x &lt;= VV}) | v == xs}</span><span class='hs-varid'>xs</span></a></span>
</pre>

This is thoroughly perplexing, but again, is explained by the absence of 
parametricity. When we *remove* the type signature, GHC defaults to giving 
`go` a *monomorphic* signature where the `a` is not universally quantified, 
and which roughly captures the same specification as the monomorphic `insertM` 
above causing verification to fail! 

Restoring the signature provides LH with the polymorphic specification, 
which can be instantiated at the call-site to recover the fact `(c)` 
that is crucial for verification.


Moral
-----

I hope that example illustrates two points.

First, *parametric polymorphism* lets type specifications 
say a lot more than they immediately let on: so do write 
polymorphic signatures whenever possible.

Second, on a less happy note, *explaining* why fancy type 
checkers fail remains a vexing problem, whose difficulty 
is compounded by increasing the cleverness of the type 
system. 

We'd love to hear any ideas you might have to solve the 
explanation problem!
