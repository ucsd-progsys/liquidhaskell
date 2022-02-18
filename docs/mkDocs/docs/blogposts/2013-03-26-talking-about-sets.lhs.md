---
layout: post
title: Talking About Sets
date: 2013-03-26 16:12
comments: true
tags:
   - basic
   - measures
   - sets
author: Ranjit Jhala
published: true 
demo: TalkingAboutSets.hs
---

In the posts so far, we've seen how LiquidHaskell allows you to use SMT 
solvers to specify and verify *numeric* invariants -- denominators 
that are non-zero, integer indices that are within the range of an 
array, vectors that have the right number of dimensions and so on.

However, SMT solvers are not limited to numbers, and in fact, support
rather expressive logics. In the next couple of posts, let's see how
LiquidHaskell uses SMT to talk about **sets of values**, for example, 
the contents of a list, and to specify and verify properties about 
those sets.

<!-- more -->


<pre><span class=hs-linenum>27: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>TalkingAboutSets</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>28: </span>
<span class=hs-linenum>29: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>filter</span><span class='hs-layout'>,</span> <span class='hs-varid'>split</span><span class='hs-layout'>)</span>
<span class=hs-linenum>30: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span>  <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>reverse</span><span class='hs-layout'>,</span> <span class='hs-varid'>filter</span><span class='hs-layout'>)</span>
<span class=hs-linenum>31: </span>
</pre>

Talking about Sets (In Logic)
=============================

First, we need a way to talk about sets in the refinement logic. We could
roll our own special Haskell type, but why not just use the `Set a` type
from `Data.Set`.

The `import Data.Set` , also instructs LiquidHaskell to import in the various 
specifications defined for the `Data.Set` module that we have *predefined* 
in [Data/Set.spec][setspec] 

 Let's look at the specifications.
<pre><span class=hs-linenum>46: </span><span class='hs-keyword'>module</span> <span class='hs-varid'>spec</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>47: </span>
<span class=hs-linenum>48: </span><span class='hs-definition'>embed</span> <span class='hs-conid'>Set</span> <span class='hs-keyword'>as</span> <span class='hs-conid'>Set_Set</span>
</pre>

The `embed` directive tells LiquidHaskell to model the **Haskell** 
type constructor `Set` with the **SMT** type constructor `Set_Set`.

 First, we define the logical operators (i.e. `measure`s) 
<pre><span class=hs-linenum>55: </span><span class='hs-definition'>measure</span> <span class='hs-conid'>Set_sng</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>                    <span class='hs-comment'>-- ^ singleton</span>
<span class=hs-linenum>56: </span><span class='hs-definition'>measure</span> <span class='hs-conid'>Set_cup</span>  <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>   <span class='hs-comment'>-- ^ union</span>
<span class=hs-linenum>57: </span><span class='hs-definition'>measure</span> <span class='hs-conid'>Set_cap</span>  <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>   <span class='hs-comment'>-- ^ intersection</span>
<span class=hs-linenum>58: </span><span class='hs-definition'>measure</span> <span class='hs-conid'>Set_dif</span>  <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>   <span class='hs-comment'>-- ^ difference </span>
</pre>

 Next, we define predicates on `Set`s 
<pre><span class=hs-linenum>62: </span><span class='hs-definition'>measure</span> <span class='hs-conid'>Set_emp</span>  <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span>                 <span class='hs-comment'>-- ^ emptiness</span>
<span class=hs-linenum>63: </span><span class='hs-definition'>measure</span> <span class='hs-conid'>Set_mem</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span>            <span class='hs-comment'>-- ^ membership</span>
<span class=hs-linenum>64: </span><span class='hs-definition'>measure</span> <span class='hs-conid'>Set_sub</span>  <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span>      <span class='hs-comment'>-- ^ inclusion </span>
</pre>


Interpreted Operations
----------------------

The above operators are *interpreted* by the SMT solver. 

 That is, just like the SMT solver "knows that"
<pre><span class=hs-linenum>74: </span><span class='hs-num'>2</span> <span class='hs-varop'>+</span> <span class='hs-num'>2</span> <span class='hs-varop'>==</span> <span class='hs-num'>4</span>
</pre>

 the SMT solver also "knows that"
<pre><span class=hs-linenum>78: </span><span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varop'>==</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cap</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cup</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-num'>2</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-num'>1</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
</pre>

This is because, the above formulas belong to a decidable Theory of Sets
which can be reduced to McCarthy's more general [Theory of Arrays][mccarthy]. 
See [this recent paper][z3cal] if you want to learn more about how modern SMT 
solvers "know" the above equality holds...

Talking about Sets (In Code)
============================

Of course, the above operators exist purely in the realm of the 
refinement logic, beyond the grasp of the programmer.

To bring them down (or up, or left or right) within reach of Haskell code, 
we can simply *assume* that the various public functions in `Data.Set` do 
the *Right Thing* i.e. produce values that reflect the logical set operations:

 First, the functions that create `Set` values
<pre><span class=hs-linenum>97: </span><span class='hs-definition'>empty</span>     <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_emp</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>98: </span><span class='hs-definition'>singleton</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>

 Next, the functions that operate on elements and `Set` values
<pre><span class=hs-linenum>102: </span><span class='hs-definition'>insert</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> 
<span class=hs-linenum>103: </span>                <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>104: </span>                <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cup</span> <span class='hs-varid'>xs</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>105: </span>
<span class=hs-linenum>106: </span><span class='hs-definition'>delete</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> 
<span class=hs-linenum>107: </span>                <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>108: </span>                <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_dif</span> <span class='hs-varid'>xs</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>

 Then, the binary `Set` operators
<pre><span class=hs-linenum>112: </span><span class='hs-definition'>union</span>        <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>113: </span>                      <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>114: </span>                      <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cup</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>115: </span>
<span class=hs-linenum>116: </span><span class='hs-definition'>intersection</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>117: </span>                      <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>118: </span>                      <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cap</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>119: </span>
<span class=hs-linenum>120: </span><span class='hs-definition'>difference</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>121: </span>                      <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>122: </span>                      <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_dif</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>

 And finally, the predicates on `Set` values:
<pre><span class=hs-linenum>126: </span><span class='hs-definition'>isSubsetOf</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>127: </span>                    <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>128: </span>                    <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Bool</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conid'>Prop</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-varop'>&lt;=&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sub</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>129: </span>
<span class=hs-linenum>130: </span><span class='hs-definition'>member</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> 
<span class=hs-linenum>131: </span>                    <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>132: </span>                    <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Bool</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conid'>Prop</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-varop'>&lt;=&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_mem</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>

**Note:** Of course we shouldn't and needn't really *assume*, but should and
will *guarantee* that the functions from `Data.Set` implement the above types. 
But thats a story for another day...

Proving Theorems With LiquidHaskell
===================================

OK, let's take our refined operators from `Data.Set` out for a spin!
One pleasant consequence of being able to precisely type the operators 
from `Data.Set` is that we have a pleasant interface for using the SMT
solver to *prove theorems* about sets, while remaining firmly rooted in
Haskell. 

First, let's write a simple function that asserts that its input is `True`


<pre><span class=hs-linenum>151: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>boolAssert</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Bool</span> <span class='hs-keyword'>| (Prop v)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Bool</span> <span class='hs-keyword'>| (Prop v)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>152: </span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV]))}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV]))}</span><span class='hs-definition'>boolAssert</span></a> <span class='hs-conid'>True</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV])),(VV = True)}</span><span class='hs-conid'>True</span></a>
<span class=hs-linenum>153: </span><span class='hs-definition'>boolAssert</span> <span class='hs-conid'>False</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[(GHC.Types.Char)] -&gt; {VV : (GHC.Types.Bool) | false}</span><span class='hs-varid'>error</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"boolAssert: False? Never!"</span></a>
</pre>

Now, we can use `boolAssert` to write some simple properties. (Yes, these do
indeed look like QuickCheck properties -- but here, instead of generating
tests and executing the code, the type system is proving to us that the
properties will *always* evaluate to `True`) 

Let's check that `intersection` is commutative ...


<pre><span class=hs-linenum>164: </span><a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
(Data.Set.Base.Set a) -&gt; (Data.Set.Base.Set a) -&gt; (GHC.Types.Bool)</span><span class='hs-definition'>prop_cap_comm</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set a)</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set a)</span><span class='hs-varid'>y</span></a> 
<span class=hs-linenum>165: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV]))}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV]))}</span><span class='hs-varid'>boolAssert</span></a> 
<span class=hs-linenum>166: </span>  <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}
 -&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)})
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Bool)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set a)
-&gt; ys:(Data.Set.Base.Set a)
-&gt; {VV : (Data.Set.Base.Set a) | (VV = Set_cap([xs; ys]))}</span><span class='hs-varop'>`intersection`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = y)}</span><span class='hs-varid'>y</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>GHC.Classes.Eq (Data.Set.Base.Set a)</span><span class='hs-varop'>==</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set a)
-&gt; ys:(Data.Set.Base.Set a)
-&gt; {VV : (Data.Set.Base.Set a) | (VV = Set_cap([xs; ys]))}</span><span class='hs-varop'>`intersection`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span>
</pre>

that `union` is associative ...


<pre><span class=hs-linenum>172: </span><a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
(Data.Set.Base.Set a)
-&gt; (Data.Set.Base.Set a)
-&gt; (Data.Set.Base.Set a)
-&gt; (GHC.Types.Bool)</span><span class='hs-definition'>prop_cup_assoc</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set a)</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set a)</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set a)</span><span class='hs-varid'>z</span></a> 
<span class=hs-linenum>173: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV]))}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV]))}</span><span class='hs-varid'>boolAssert</span></a> 
<span class=hs-linenum>174: </span>  <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}
 -&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)})
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Bool)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set a)
-&gt; ys:(Data.Set.Base.Set a)
-&gt; {VV : (Data.Set.Base.Set a) | (VV = Set_cup([xs; ys]))}</span><span class='hs-varop'>`union`</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set a)
-&gt; ys:(Data.Set.Base.Set a)
-&gt; {VV : (Data.Set.Base.Set a) | (VV = Set_cup([xs; ys]))}</span><span class='hs-varop'>`union`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = z)}</span><span class='hs-varid'>z</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>GHC.Classes.Eq (Data.Set.Base.Set a)</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set a)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set a)
-&gt; ys:(Data.Set.Base.Set a)
-&gt; {VV : (Data.Set.Base.Set a) | (VV = Set_cup([xs; ys]))}</span><span class='hs-varop'>`union`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = y)}</span><span class='hs-varid'>y</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set a)
-&gt; ys:(Data.Set.Base.Set a)
-&gt; {VV : (Data.Set.Base.Set a) | (VV = Set_cup([xs; ys]))}</span><span class='hs-varop'>`union`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = z)}</span><span class='hs-varid'>z</span></a>
</pre>

and that `union` distributes over `intersection`.


<pre><span class=hs-linenum>180: </span><a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
(Data.Set.Base.Set a)
-&gt; (Data.Set.Base.Set a)
-&gt; (Data.Set.Base.Set a)
-&gt; (GHC.Types.Bool)</span><span class='hs-definition'>prop_cap_dist</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set a)</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set a)</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set a)</span><span class='hs-varid'>z</span></a> 
<span class=hs-linenum>181: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV]))}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV]))}</span><span class='hs-varid'>boolAssert</span></a> 
<span class=hs-linenum>182: </span>  <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}
 -&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)})
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}</span><span class='hs-varop'>$</span></a>  <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set a)
-&gt; ys:(Data.Set.Base.Set a)
-&gt; {VV : (Data.Set.Base.Set a) | (VV = Set_cap([xs; ys]))}</span><span class='hs-varop'>`intersection`</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set a)
-&gt; ys:(Data.Set.Base.Set a)
-&gt; {VV : (Data.Set.Base.Set a) | (VV = Set_cup([xs; ys]))}</span><span class='hs-varop'>`union`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = z)}</span><span class='hs-varid'>z</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>183: </span>  <a class=annot href="#"><span class=annottext>GHC.Classes.Eq (Data.Set.Base.Set a)</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set a)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set a)
-&gt; ys:(Data.Set.Base.Set a)
-&gt; {VV : (Data.Set.Base.Set a) | (VV = Set_cap([xs; ys]))}</span><span class='hs-varop'>`intersection`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = y)}</span><span class='hs-varid'>y</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set a)
-&gt; ys:(Data.Set.Base.Set a)
-&gt; {VV : (Data.Set.Base.Set a) | (VV = Set_cup([xs; ys]))}</span><span class='hs-varop'>`union`</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set a)
-&gt; ys:(Data.Set.Base.Set a)
-&gt; {VV : (Data.Set.Base.Set a) | (VV = Set_cap([xs; ys]))}</span><span class='hs-varop'>`intersection`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = z)}</span><span class='hs-varid'>z</span></a><span class='hs-layout'>)</span> 
</pre>
  
Of course, while we're at it, let's make sure LiquidHaskell
doesn't prove anything that *isn't* true ...


<pre><span class=hs-linenum>190: </span><a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
(Data.Set.Base.Set a) -&gt; (Data.Set.Base.Set a) -&gt; (GHC.Types.Bool)</span><span class='hs-definition'>prop_cup_dif_bad</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set a)</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set a)</span><span class='hs-varid'>y</span></a>
<span class=hs-linenum>191: </span>   <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV]))}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV]))}</span><span class='hs-varid'>boolAssert</span></a></span> 
<span class=hs-linenum>192: </span>   <a class=annot href="#"><span class=annottext>((GHC.Types.Bool)
 -&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)})
-&gt; (GHC.Types.Bool)
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>GHC.Classes.Eq (Data.Set.Base.Set a)</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set a)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set a)
-&gt; ys:(Data.Set.Base.Set a)
-&gt; {VV : (Data.Set.Base.Set a) | (VV = Set_cup([xs; ys]))}</span><span class='hs-varop'>`union`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = y)}</span><span class='hs-varid'>y</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set a)
-&gt; ys:(Data.Set.Base.Set a)
-&gt; {VV : (Data.Set.Base.Set a) | (VV = Set_dif([xs; ys]))}</span><span class='hs-varop'>`difference`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set a) | (VV = y)}</span><span class='hs-varid'>y</span></a>
</pre>

Hmm. You do know why the above doesn't hold, right? It would be nice to
get a *counterexample* wouldn't it? Well, for the moment, there is
QuickCheck!

Thus, the refined types offer a nice interface for interacting with the SMT
solver in order to prove theorems in LiquidHaskell. (BTW, The [SBV project][sbv]
describes another approach for using SMT solvers from Haskell, without the 
indirection of refinement types.)

While the above is a nice warm up exercise to understanding how
LiquidHaskell reasons about sets, our overall goal is not to prove 
theorems about set operators, but instead to specify and verify 
properties of programs. 



The Set of Values in a List
===========================

Let's see how we might reason about sets of values in regular Haskell programs.

We'll begin with Lists, the jack-of-all-data-types. Now, instead of just
talking about the **number of** elements in a list, we can write a measure
that describes the **set of** elements in a list:

 A measure for the elements of a list, from [Data/Set.spec][setspec]
<pre><span class=hs-linenum>221: </span>
<span class=hs-linenum>222: </span><span class='hs-definition'>measure</span> <span class='hs-varid'>listElts</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>223: </span><span class='hs-definition'>listElts</span> <span class='hs-layout'>(</span><span class='hs-conid'>[]</span><span class='hs-layout'>)</span>    <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varop'>?</span> <span class='hs-conid'>Set_emp</span><span class='hs-layout'>(</span><span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>224: </span><span class='hs-definition'>listElts</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span>  <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cup</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-layout'>}</span>
</pre>

That is, `(listElts xs)` describes the set of elements contained in a list `xs`.

Next, to make the specifications concise, let's define a few predicate aliases:


<pre><span class=hs-linenum>232: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>EqElts</span>  <span class='hs-conid'>X</span> <span class='hs-conid'>Y</span> <span class='hs-keyglyph'>=</span> 
<span class=hs-linenum>233: </span>      <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>Y</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>                        <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>234: </span>
<span class=hs-linenum>235: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>SubElts</span>   <span class='hs-conid'>X</span> <span class='hs-conid'>Y</span> <span class='hs-keyglyph'>=</span> 
<span class=hs-linenum>236: </span>      <span class='hs-layout'>(</span><span class='hs-conid'>Set_sub</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>Y</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>                  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>237: </span>
<span class=hs-linenum>238: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>UnionElts</span> <span class='hs-conid'>X</span> <span class='hs-conid'>Y</span> <span class='hs-conid'>Z</span> <span class='hs-keyglyph'>=</span> 
<span class=hs-linenum>239: </span>      <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cup</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>Y</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>Z</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>

A Trivial Identity
------------------

OK, now let's write some code to check that the `listElts` measure is sensible!


<pre><span class=hs-linenum>248: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>listId</span>    <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (EqElts v xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>249: </span><a class=annot href="#"><span class=annottext>forall a.
x1:[a]
-&gt; {VV : [a] | (len([VV]) = len([x1])),
               (listElts([VV]) = Set_cup([listElts([x1]); listElts([x1])])),
               (listElts([VV]) = listElts([x1])),
               (listElts([x1]) = Set_cup([listElts([x1]); listElts([VV])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-definition'>listId</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
{VV : [{VV : a | false}]&lt;p&gt; | (? Set_emp([listElts([VV])])),
                              (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>250: </span><span class='hs-definition'>listId</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p y&gt;]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (len([VV]) = (1 + len([ys]))),
                  (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
x1:[a]
-&gt; {VV : [a] | (len([VV]) = len([x1])),
               (listElts([VV]) = Set_cup([listElts([x1]); listElts([x1])])),
               (listElts([VV]) = listElts([x1])),
               (listElts([x1]) = Set_cup([listElts([x1]); listElts([VV])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>listId</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

That is, LiquidHaskell checks that the set of elements of the output list
is the same as those in the input.

A Less Trivial Identity
-----------------------

Next, let's write a function to `reverse` a list. Of course, we'd like to
verify that `reverse` doesn't leave any elements behind; that is that the 
output has the same set of values as the input list. This is somewhat more 
interesting because of the *tail recursive* helper `go`. Do you understand 
the type that is inferred for it? (Put your mouse over `go` to see the 
inferred type.)


<pre><span class=hs-linenum>267: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reverse</span>       <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (EqElts v xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>268: </span><a class=annot href="#"><span class=annottext>forall a. xs:[a] -&gt; {VV : [a] | (listElts([VV]) = listElts([xs]))}</span><span class='hs-definition'>reverse</span></a>           <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (len([VV]) = 0)}
-&gt; x2:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([x1]);
                                          listElts([x2])])),
               (listElts([VV]) = Set_cup([listElts([x2]); listElts([x1])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (? Set_emp([listElts([VV])])),
                                           (len([VV]) = 0),
                                           (len([VV]) &gt;= 0)}</span><span class='hs-conid'>[]</span></a> 
<span class=hs-linenum>269: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>270: </span>    <a class=annot href="#"><span class=annottext>acc:{VV : [a] | (len([VV]) &gt;= 0)}
-&gt; x1:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([acc]);
                                          listElts([x1])])),
               (listElts([VV]) = Set_cup([listElts([x1]); listElts([acc])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>acc</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = acc),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>acc</span></a>
<span class=hs-linenum>271: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>acc</span> <span class='hs-layout'>(</span><span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>ys</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>acc:{VV : [a] | (len([VV]) &gt;= 0)}
-&gt; x1:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([acc]);
                                          listElts([x1])])),
               (listElts([VV]) = Set_cup([listElts([x1]); listElts([acc])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>go</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p y&gt;]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (len([VV]) = (1 + len([ys]))),
                  (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = acc),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>acc</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
</pre>

Appending Lists
---------------

Next, here's good old `append`, but now with a specification that states
that the output indeed includes the elements from both the input lists.


<pre><span class=hs-linenum>281: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>append</span>       <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-keyword'>| (UnionElts v xs ys)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>282: </span><a class=annot href="#"><span class=annottext>forall a.
x1:[a]
-&gt; ys:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([x1]);
                                          listElts([ys])])),
               (listElts([VV]) = Set_cup([listElts([ys]); listElts([x1])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-definition'>append</span></a> <span class='hs-conid'>[]</span>     <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>ys</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
<span class=hs-linenum>283: </span><span class='hs-definition'>append</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varid'>ys</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p y&gt;]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (len([VV]) = (1 + len([ys]))),
                  (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
x1:[a]
-&gt; ys:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([x1]);
                                          listElts([ys])])),
               (listElts([VV]) = Set_cup([listElts([ys]); listElts([x1])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>append</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
</pre>

Filtering Lists
---------------

Let's round off the list trilogy, with `filter`. Here, we can verify
that it returns a **subset of** the values of the input list.


<pre><span class=hs-linenum>293: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>filter</span>      <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-keyword'>| (SubElts v xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>294: </span>
<span class=hs-linenum>295: </span><a class=annot href="#"><span class=annottext>forall a.
(a -&gt; (GHC.Types.Bool))
-&gt; x2:[a]
-&gt; {VV : [a] | (? Set_sub([listElts([VV]); listElts([x2])])),
               (listElts([x2]) = Set_cup([listElts([x2]); listElts([VV])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-definition'>filter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>f</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
{VV : [{VV : a | false}]&lt;p&gt; | (? Set_emp([listElts([VV])])),
                              (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>296: </span><span class='hs-definition'>filter</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>297: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p y&gt;]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (len([VV]) = (1 + len([ys]))),
                  (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
(a -&gt; (GHC.Types.Bool))
-&gt; x2:[a]
-&gt; {VV : [a] | (? Set_sub([listElts([VV]); listElts([x2])])),
               (listElts([x2]) = Set_cup([listElts([x2]); listElts([VV])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> 
<span class=hs-linenum>298: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
(a -&gt; (GHC.Types.Bool))
-&gt; x2:[a]
-&gt; {VV : [a] | (? Set_sub([listElts([VV]); listElts([x2])])),
               (listElts([x2]) = Set_cup([listElts([x2]); listElts([VV])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

Merge Sort
==========

Let's conclude this entry with one larger example: `mergeSort`.
We'd like to verify that, well, the list that is returned 
contains the same set of elements as the input list. 

And so we will!

But first, let's remind ourselves of how `mergeSort` works:

1. `split` the input list into two halves, 
2. `sort`  each half, recursively, 
3. `merge` the sorted halves to obtain the sorted list.


Split
-----

We can `split` a list into two, roughly equal parts like so:


<pre><span class=hs-linenum>323: </span><a class=annot href="#"><span class=annottext>forall a.
x1:[a]
-&gt; ({VV : [a] | (? Set_sub([listElts([VV]); listElts([x1])])),
                (listElts([x1]) = Set_cup([listElts([x1]); listElts([VV])])),
                (len([VV]) &gt;= 0)} , {VV : [a] | (? Set_sub([listElts([VV]);
                                                            listElts([x1])])),
                                                (listElts([x1]) = Set_cup([listElts([x1]);
                                                                           listElts([VV])])),
                                                (len([VV]) &gt;= 0)})&lt;\x1 VV -&gt; (? Set_sub([listElts([VV]);
                                                                                         listElts([x1])])),
                                                                             (listElts([x1]) = Set_cup([listElts([x1]);
                                                                                                        listElts([VV])])),
                                                                             (listElts([x1]) = Set_cup([listElts([x1]);
                                                                                                        listElts([VV])])),
                                                                             (len([VV]) &gt;= 0)&gt;</span><span class='hs-definition'>split</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a -&gt; b -&gt; Bool&gt;. x1:a -&gt; b&lt;p2 x1&gt; -&gt; (a , b)&lt;p2&gt;</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (? Set_emp([listElts([VV])])),
                                           (len([VV]) = 0),
                                           (len([VV]) &gt;= 0)}</span><span class='hs-conid'>[]</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (? Set_emp([listElts([VV])])),
                                           (len([VV]) = 0),
                                           (len([VV]) &gt;= 0)}</span><span class='hs-conid'>[]</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>324: </span><span class='hs-definition'>split</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a -&gt; b -&gt; Bool&gt;. x1:a -&gt; b&lt;p2 x1&gt; -&gt; (a , b)&lt;p2&gt;</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p y&gt;]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (len([VV]) = (1 + len([ys]))),
                  (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (? Set_sub([listElts([VV]); listElts([xs])])),
            (VV = zs),
            (VV = zs),
            (len([VV]) = len([zs])),
            (listElts([VV]) = Set_cup([listElts([zs]); listElts([zs])])),
            (listElts([VV]) = listElts([zs])),
            (listElts([xs]) = Set_cup([listElts([xs]); listElts([VV])])),
            (listElts([xs]) = Set_cup([listElts([ys]); listElts([VV])])),
            (listElts([xs]) = Set_cup([listElts([ys]); listElts([VV])])),
            (listElts([zs]) = Set_cup([listElts([zs]); listElts([VV])])),
            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>zs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (? Set_sub([listElts([VV]); listElts([xs])])),
            (VV = ys),
            (VV = ys),
            (len([VV]) = len([ys])),
            (listElts([VV]) = Set_cup([listElts([ys]); listElts([ys])])),
            (listElts([VV]) = listElts([ys])),
            (listElts([xs]) = Set_cup([listElts([xs]); listElts([VV])])),
            (listElts([xs]) = Set_cup([listElts([zs]); listElts([VV])])),
            (listElts([ys]) = Set_cup([listElts([ys]); listElts([VV])])),
            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>325: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>326: </span>    <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (? Set_sub([listElts([VV]); listElts([xs])])),
            (VV = ys),
            (len([VV]) = len([ys])),
            (listElts([VV]) = Set_cup([listElts([ys]); listElts([ys])])),
            (listElts([VV]) = listElts([ys])),
            (listElts([xs]) = Set_cup([listElts([xs]); listElts([VV])])),
            (listElts([xs]) = Set_cup([listElts([zs]); listElts([VV])])),
            (listElts([ys]) = Set_cup([listElts([ys]); listElts([VV])])),
            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (? Set_sub([listElts([VV]); listElts([xs])])),
            (VV = zs),
            (len([VV]) = len([zs])),
            (listElts([VV]) = Set_cup([listElts([zs]); listElts([zs])])),
            (listElts([VV]) = listElts([zs])),
            (listElts([xs]) = Set_cup([listElts([xs]); listElts([VV])])),
            (listElts([xs]) = Set_cup([listElts([ys]); listElts([VV])])),
            (listElts([xs]) = Set_cup([listElts([ys]); listElts([VV])])),
            (listElts([zs]) = Set_cup([listElts([zs]); listElts([VV])])),
            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>zs</span></a><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
x1:[a]
-&gt; ({VV : [a] | (? Set_sub([listElts([VV]); listElts([x1])])),
                (listElts([x1]) = Set_cup([listElts([x1]); listElts([VV])])),
                (len([VV]) &gt;= 0)} , {VV : [a] | (? Set_sub([listElts([VV]);
                                                            listElts([x1])])),
                                                (listElts([x1]) = Set_cup([listElts([x1]);
                                                                           listElts([VV])])),
                                                (len([VV]) &gt;= 0)})&lt;\x1 VV -&gt; (? Set_sub([listElts([VV]);
                                                                                         listElts([x1])])),
                                                                             (listElts([x1]) = Set_cup([listElts([x1]);
                                                                                                        listElts([VV])])),
                                                                             (listElts([x1]) = Set_cup([listElts([x1]);
                                                                                                        listElts([VV])])),
                                                                             (len([VV]) &gt;= 0)&gt;</span><span class='hs-varid'>split</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

LiquidHaskell verifies that the relevant property of split is

 
<pre><span class=hs-linenum>332: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>split</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-layout'>,</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-layout'>)</span><span class='hs-keyword'>&lt;{\ys zs -&gt; (UnionElts xs ys zs)}&gt;</span> <span class='hs-keyword'>@-}</span>
</pre>

The funny syntax with angle brackets simply says that the output of `split` 
is a *pair* `(ys, zs)` whose union is the list of elements of the input `xs`.
(Yes, this is indeed a dependent pair; we will revisit these later to
understand whats going on with the odd syntax.)

Merge
-----

Next, we can `merge` two (sorted) lists like so:


<pre><span class=hs-linenum>346: </span><a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
xs:[a]
-&gt; x1:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([x1]);
                                          listElts([xs])])),
               (listElts([VV]) = Set_cup([listElts([xs]); listElts([x1])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-definition'>merge</span></a> <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>xs</span></a> <span class='hs-conid'>[]</span>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>347: </span><span class='hs-definition'>merge</span> <span class='hs-conid'>[]</span> <span class='hs-varid'>ys</span>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
<span class=hs-linenum>348: </span><span class='hs-definition'>merge</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>ys</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>349: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:a
-&gt; y:a -&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a>          <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p y&gt;]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (len([VV]) = (1 + len([ys]))),
                  (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
xs:[a]
-&gt; x1:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([x1]);
                                          listElts([xs])])),
               (listElts([VV]) = Set_cup([listElts([xs]); listElts([x1])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>merge</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p y&gt;]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (len([VV]) = (1 + len([ys]))),
                  (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>350: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p y&gt;]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (len([VV]) = (1 + len([ys]))),
                  (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
xs:[a]
-&gt; x1:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([x1]);
                                          listElts([xs])])),
               (listElts([VV]) = Set_cup([listElts([xs]); listElts([x1])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>merge</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p y&gt;]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (len([VV]) = (1 + len([ys]))),
                  (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
</pre>

As you might expect, the elements of the returned list are the union of the
elements of the input, or as LiquidHaskell might say,


<pre><span class=hs-linenum>357: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>merge</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-keyword'>| (UnionElts v x y)}</span> <span class='hs-keyword'>@-}</span>
</pre>

Sort
----

Finally, we put all the pieces together by


<pre><span class=hs-linenum>366: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>mergeSort</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (EqElts v xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>367: </span><a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
x1:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([x1]);
                                          listElts([x1])])),
               (listElts([VV]) = listElts([x1])),
               (listElts([x1]) = Set_cup([listElts([x1]); listElts([VV])]))}</span><span class='hs-definition'>mergeSort</span></a> <span class='hs-conid'>[]</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
{VV : [{VV : a | false}]&lt;p&gt; | (? Set_emp([listElts([VV])])),
                              (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>368: </span><span class='hs-definition'>mergeSort</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (? Set_emp([listElts([VV])])),
                                           (len([VV]) = 0),
                                           (len([VV]) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>369: </span><span class='hs-definition'>mergeSort</span> <span class='hs-varid'>xs</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:[a]
-&gt; y:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([x]);
                                          listElts([y])]))}</span><span class='hs-varid'>merge</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
x1:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([x1]);
                                          listElts([x1])])),
               (listElts([VV]) = listElts([x1])),
               (listElts([x1]) = Set_cup([listElts([x1]); listElts([VV])]))}</span><span class='hs-varid'>mergeSort</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),
            (VV = ys),
            (len([VV]) = len([ys])),
            (listElts([VV]) = Set_cup([listElts([ys]); listElts([ys])])),
            (listElts([VV]) = listElts([ys])),
            (listElts([ys]) = Set_cup([listElts([ys]); listElts([VV])])),
            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
x1:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([x1]);
                                          listElts([x1])])),
               (listElts([VV]) = listElts([x1])),
               (listElts([x1]) = Set_cup([listElts([x1]); listElts([VV])]))}</span><span class='hs-varid'>mergeSort</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = zs),
            (VV = zs),
            (len([VV]) = len([zs])),
            (listElts([VV]) = Set_cup([listElts([zs]); listElts([zs])])),
            (listElts([VV]) = listElts([zs])),
            (listElts([zs]) = Set_cup([listElts([zs]); listElts([VV])])),
            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>zs</span></a><span class='hs-layout'>)</span> 
<span class=hs-linenum>370: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>371: </span>    <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),
            (len([VV]) = len([ys])),
            (listElts([VV]) = Set_cup([listElts([ys]); listElts([ys])])),
            (listElts([VV]) = listElts([ys])),
            (listElts([ys]) = Set_cup([listElts([ys]); listElts([VV])])),
            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = zs),
            (len([VV]) = len([zs])),
            (listElts([VV]) = Set_cup([listElts([zs]); listElts([zs])])),
            (listElts([VV]) = listElts([zs])),
            (listElts([zs]) = Set_cup([listElts([zs]); listElts([VV])])),
            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>zs</span></a><span class='hs-layout'>)</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>xs:[a]
-&gt; ([a] , [a])&lt;\ys VV -&gt; (listElts([xs]) = Set_cup([listElts([ys]);
                                                    listElts([VV])]))&gt;</span><span class='hs-varid'>split</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

The type given to `mergeSort`guarantees that the set of elements in the 
output list is indeed the same as in the input list. Of course, it says 
nothing about whether the list is *actually sorted*. 

Well, Rome wasn't built in a day...

[sbv]:      https://github.com/LeventErkok/sbv
[setspec]:  https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/Set.spec
[mccarthy]: http://www-formal.stanford.edu/jmc/towards.ps
[z3cal]:    http://research.microsoft.com/en-us/um/people/leonardo/fmcad09.pdf
