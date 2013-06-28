---
layout: post
title: "Lets Talk About Sets"
date: 2013-01-05 16:12
comments: true
external-url:
categories: basic, measures, sets
author: Ranjit Jhala
published: false 
---

In the posts so far, we've seen how LiquidHaskell allows you to use SMT 
solvers to specify and verify *numeric* invariants -- denominators 
that are non-zero, integer indices that are within the range of an 
array, vectors that have the right number of dimensions and so on.

However, SMT solvers are not limited to numbers, and in fact, support
rather expressive logics. In the next couple of posts, lets see how 
LiquidHaskell uses SMT to talk about **sets of values**, for example, 
the contents of a list, and to specify and verify properties about 
those sets.


<pre><span class=hs-linenum>24: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>ListSets</span> <span class='hs-keyword'>where</span>
</pre>

Talking about Sets (In Logic)
=============================

First, we need a way to talk about sets in the refinement logic. We could
roll our own special Haskell type, but why not just use the `Set a` type
from `Data.Set`.


<pre><span class=hs-linenum>35: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>filter</span><span class='hs-layout'>,</span> <span class='hs-varid'>split</span><span class='hs-layout'>)</span>
<span class=hs-linenum>36: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span>  <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>reverse</span><span class='hs-layout'>,</span> <span class='hs-varid'>filter</span><span class='hs-layout'>)</span>
</pre>

The above, also instructs LiquidHaskell to import in the various 
specifications defined for the `Data.Set` module that we have *predefined* 
in [Data/Set.spec][setspec] 

Lets look at the specifications.

 The `embed` directive tells LiquidHaskell to model the **Haskell** 
<pre><span class=hs-linenum>46: </span><span class='hs-keyword'>type</span> <span class='hs-varid'>constructor</span> <span class='hs-varop'>`Set`</span> <span class='hs-varid'>with</span> <span class='hs-varid'>the</span> <span class='hs-varop'>**</span><span class='hs-conid'>SMT</span><span class='hs-varop'>**</span> <span class='hs-keyword'>type</span> <span class='hs-varid'>constructor</span> <span class='hs-varop'>`Set_Set`</span><span class='hs-varop'>.</span>
<span class=hs-linenum>47: </span>
<span class=hs-linenum>48: </span><span class='hs-keyword'>module</span> <span class='hs-varid'>spec</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>49: </span>
<span class=hs-linenum>50: </span><span class='hs-definition'>embed</span> <span class='hs-conid'>Set</span> <span class='hs-keyword'>as</span> <span class='hs-conid'>Set_Set</span>
</pre>

 First, we define the logical operators (i.e. `measure`s) 
<pre><span class=hs-linenum>54: </span><span class='hs-definition'>measure</span> <span class='hs-conid'>Set_sng</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>                    <span class='hs-comment'>-- ^ singleton</span>
<span class=hs-linenum>55: </span><span class='hs-definition'>measure</span> <span class='hs-conid'>Set_cup</span>  <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>   <span class='hs-comment'>-- ^ union</span>
<span class=hs-linenum>56: </span><span class='hs-definition'>measure</span> <span class='hs-conid'>Set_cap</span>  <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>   <span class='hs-comment'>-- ^ intersection</span>
<span class=hs-linenum>57: </span><span class='hs-definition'>measure</span> <span class='hs-conid'>Set_dif</span>  <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>   <span class='hs-comment'>-- ^ difference </span>
</pre>

 Next, we define predicates on `Set`s 
<pre><span class=hs-linenum>61: </span><span class='hs-definition'>measure</span> <span class='hs-conid'>Set_emp</span>  <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span>                 <span class='hs-comment'>-- ^ emptiness</span>
<span class=hs-linenum>62: </span><span class='hs-definition'>measure</span> <span class='hs-conid'>Set_mem</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span>            <span class='hs-comment'>-- ^ membership</span>
<span class=hs-linenum>63: </span><span class='hs-definition'>measure</span> <span class='hs-conid'>Set_sub</span>  <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span>      <span class='hs-comment'>-- ^ inclusion </span>
</pre>


Interpreted Operations
----------------------

The above operators are *interpreted* by the SMT solver. That is, just 
like the SMT solver *"knows that"* 

    2 + 2 == 4

the SMT solver *"knows that"* 

    (Set_sng 1) == (Set_cap (Set_sng 1) (Set_cup (Set_sng 2) (Set_sng 1)))

This is because, the above formulas belong to a decidable Theory of Sets
which can be reduced to McCarthy's more general [Theory of Arrays][mccarthy]. 
See [this recent paper][z3cal] if you want to learn more about how modern SMT 
solvers *"know"* the above equality holds...

Talking about Sets (In Code)
============================

Of course, the above operators exist purely in the realm of the 
refinement logic, beyond the grasp of the programmer.

To bring them down (or up, or left or right) within reach of Haskell code, 
we can simply *assume* that the various public functions in `Data.Set` do 
the *Right Thing* i.e. produce values that reflect the logical set operations:

 First, the functions that create `Set` values
<pre><span class=hs-linenum>95: </span><span class='hs-definition'>empty</span>     <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_emp</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>96: </span><span class='hs-definition'>singleton</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>

 Next, the functions that operate on elements and `Set` values
<pre><span class=hs-linenum>100: </span><span class='hs-definition'>insert</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cup</span> <span class='hs-varid'>xs</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>101: </span><span class='hs-definition'>delete</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_dif</span> <span class='hs-varid'>xs</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>

 Then, the binary `Set` operators
<pre><span class=hs-linenum>105: </span><span class='hs-definition'>union</span>        <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cup</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>106: </span><span class='hs-definition'>intersection</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cap</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>107: </span><span class='hs-definition'>difference</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_dif</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>

 And finally, the predicates on `Set` values:
<pre><span class=hs-linenum>111: </span><span class='hs-definition'>isSubsetOf</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Bool</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conid'>Prop</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-varop'>&lt;=&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sub</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>112: </span><span class='hs-definition'>member</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Bool</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conid'>Prop</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-varop'>&lt;=&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_mem</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>

**Note:** Oh quite. We shouldn't and needn't really *assume*, but should and
will *guarantee* that the functions from `Data.Set` implement the above types. 
But thats a story for another day...

Proving Theorems With LiquidHaskell
===================================

OK, lets take our refined operators from `Data.Set` out for a spin!
One pleasant consequence of being able to precisely type the operators 
from `Data.Set` is that we have a pleasant interface for using the SMT
solver to *prove theorems* about sets, while remaining firmly rooted in
Haskell. 

First, lets write a simple function that asserts that its input is `True`


<pre><span class=hs-linenum>131: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>boolAssert</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Bool</span> <span class='hs-keyword'>| (Prop v)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Bool</span> <span class='hs-keyword'>| (Prop v)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>132: </span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV]))}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV]))}</span><span class='hs-definition'>boolAssert</span></a> <span class='hs-conid'>True</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV])),(VV = True)}</span><span class='hs-conid'>True</span></a>
<span class=hs-linenum>133: </span><span class='hs-definition'>boolAssert</span> <span class='hs-conid'>False</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[(GHC.Types.Char)] -&gt; {VV : (GHC.Types.Bool) | false}</span><span class='hs-varid'>error</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"boolAssert: False? Never!"</span></a>
</pre>

Now, we can use `boolAssert` to write some simple properties. (Yes, these do
indeed look like QuickCheck properties -- but here, instead of generating
tests and executing the code, the type system is proving to us that the
properties will *always* evaluate to `True`) 

Lets check that `intersection` is commutative ...


<pre><span class=hs-linenum>144: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>prop_cap_comm</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>145: </span><span class='hs-definition'>prop_cap_comm</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>146: </span><a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))
-&gt; (Data.Set.Base.Set (GHC.Types.Int)) -&gt; (GHC.Types.Bool)</span><span class='hs-definition'>prop_cap_comm</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))</span><span class='hs-varid'>y</span></a> 
<span class=hs-linenum>147: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV]))}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV]))}</span><span class='hs-varid'>boolAssert</span></a> 
<span class=hs-linenum>148: </span>  <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}
 -&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)})
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Bool)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; ys:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = Set_cap([xs;
                                                              ys]))}</span><span class='hs-varop'>`intersection`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = y)}</span><span class='hs-varid'>y</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>GHC.Classes.Eq (Data.Set.Base.Set GHC.Types.Int)</span><span class='hs-varop'>==</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; ys:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = Set_cap([xs;
                                                              ys]))}</span><span class='hs-varop'>`intersection`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span>
</pre>

that `union` is associative ...


<pre><span class=hs-linenum>154: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>prop_cup_assoc</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>155: </span><span class='hs-definition'>prop_cup_assoc</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>156: </span><a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))
-&gt; (Data.Set.Base.Set (GHC.Types.Int))
-&gt; (Data.Set.Base.Set (GHC.Types.Int))
-&gt; (GHC.Types.Bool)</span><span class='hs-definition'>prop_cup_assoc</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))</span><span class='hs-varid'>z</span></a> 
<span class=hs-linenum>157: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV]))}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV]))}</span><span class='hs-varid'>boolAssert</span></a> 
<span class=hs-linenum>158: </span>  <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}
 -&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)})
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Bool)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; ys:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = Set_cup([xs;
                                                              ys]))}</span><span class='hs-varop'>`union`</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; ys:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = Set_cup([xs;
                                                              ys]))}</span><span class='hs-varop'>`union`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = z)}</span><span class='hs-varid'>z</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; y:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x = y))}</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; ys:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = Set_cup([xs;
                                                              ys]))}</span><span class='hs-varop'>`union`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = y)}</span><span class='hs-varid'>y</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; ys:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = Set_cup([xs;
                                                              ys]))}</span><span class='hs-varop'>`union`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = z)}</span><span class='hs-varid'>z</span></a>
</pre>

and that `union` distributes over `intersection`.


<pre><span class=hs-linenum>164: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>prop_cap_dist</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>165: </span><span class='hs-definition'>prop_cap_dist</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>166: </span><a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))
-&gt; (Data.Set.Base.Set (GHC.Types.Int))
-&gt; (Data.Set.Base.Set (GHC.Types.Int))
-&gt; (GHC.Types.Bool)</span><span class='hs-definition'>prop_cap_dist</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))</span><span class='hs-varid'>z</span></a> 
<span class=hs-linenum>167: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV]))}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV]))}</span><span class='hs-varid'>boolAssert</span></a> 
<span class=hs-linenum>168: </span>  <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}
 -&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)})
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}</span><span class='hs-varop'>$</span></a>  <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; ys:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = Set_cap([xs;
                                                              ys]))}</span><span class='hs-varop'>`intersection`</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; ys:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = Set_cup([xs;
                                                              ys]))}</span><span class='hs-varop'>`union`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = z)}</span><span class='hs-varid'>z</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>169: </span>  <a class=annot href="#"><span class=annottext>x:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; y:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x = y))}</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; ys:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = Set_cap([xs;
                                                              ys]))}</span><span class='hs-varop'>`intersection`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = y)}</span><span class='hs-varid'>y</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; ys:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = Set_cup([xs;
                                                              ys]))}</span><span class='hs-varop'>`union`</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; ys:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = Set_cap([xs;
                                                              ys]))}</span><span class='hs-varop'>`intersection`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = z)}</span><span class='hs-varid'>z</span></a><span class='hs-layout'>)</span> 
</pre>
  
Of course, while we're at it, lets make sure LiquidHaskell 
doesn't prove anything thats *not* true ...


<pre><span class=hs-linenum>176: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>prop_cup_dif_bad</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>177: </span><span class='hs-definition'>prop_cup_dif_bad</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>178: </span><a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))
-&gt; (Data.Set.Base.Set (GHC.Types.Int)) -&gt; (GHC.Types.Bool)</span><span class='hs-definition'>prop_cup_dif_bad</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))</span><span class='hs-varid'>y</span></a>
<span class=hs-linenum>179: </span>   <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV]))}
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV]))}</span><span class='hs-varid'>boolAssert</span></a></span> 
<span class=hs-linenum>180: </span>   <a class=annot href="#"><span class=annottext>((GHC.Types.Bool)
 -&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)})
-&gt; (GHC.Types.Bool)
-&gt; {VV : (GHC.Types.Bool) | (? Prop([VV])),(VV != False)}</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; y:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x = y))}</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>(Data.Set.Base.Set (GHC.Types.Int))</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; ys:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = Set_cup([xs;
                                                              ys]))}</span><span class='hs-varop'>`union`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = y)}</span><span class='hs-varid'>y</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>xs:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; ys:(Data.Set.Base.Set (GHC.Types.Int))
-&gt; {VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = Set_dif([xs;
                                                              ys]))}</span><span class='hs-varop'>`difference`</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Set.Base.Set (GHC.Types.Int)) | (VV = y)}</span><span class='hs-varid'>y</span></a>
</pre>

Hmm. You do know why the above doesn't hold, right? It would be nice to
get a *counterexample* wouldn't it. Well, for the moment, there is
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

Lets see how we might reason about sets of values in regular Haskell programs. 

Lets begin with Lists, the jack-of-all-data-types. Now, instead of just
talking about the **number of** elements in a list, we can write a measure
that describes the **set of** elements in a list:

 A measure for the elements of a list, from [Data/Set.spec][setspec]
<pre><span class=hs-linenum>208: </span>
<span class=hs-linenum>209: </span><span class='hs-definition'>measure</span> <span class='hs-varid'>listElts</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>210: </span><span class='hs-definition'>listElts</span> <span class='hs-layout'>(</span><span class='hs-conid'>[]</span><span class='hs-layout'>)</span>    <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varop'>?</span> <span class='hs-conid'>Set_emp</span><span class='hs-layout'>(</span><span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>211: </span><span class='hs-definition'>listElts</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span>  <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cup</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-layout'>}</span>
</pre>

That is, `(elts xs)` describes the set of elements contained in a list `xs`.

Next, to make the specifications concise, lets define a few predicate aliases:


<pre><span class=hs-linenum>219: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>SameElts</span>  <span class='hs-conid'>X</span> <span class='hs-conid'>Y</span>   <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>Y</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>                        <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>220: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>SubElts</span>   <span class='hs-conid'>X</span> <span class='hs-conid'>Y</span>   <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sub</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>Y</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>                   <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>221: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>UnionElts</span> <span class='hs-conid'>X</span> <span class='hs-conid'>Y</span> <span class='hs-conid'>Z</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cup</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>Y</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>Z</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>

A Trivial Identity
------------------

OK, now lets write some code to check that the `elts` measure is sensible!


<pre><span class=hs-linenum>230: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>listId</span>    <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-keyword'>| (SameElts v xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>231: </span><a class=annot href="#"><span class=annottext>forall a.
x1:[a]
-&gt; {VV : [a] | (len([VV]) = len([x1])),
               (listElts([VV]) = Set_cup([listElts([x1]); listElts([x1])])),
               (listElts([VV]) = listElts([x1])),
               (listElts([x1]) = Set_cup([listElts([x1]); listElts([VV])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-definition'>listId</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
{VV : [{VV : a | false}]&lt;p&gt; | (? Set_emp([listElts([VV])])),
                              (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>232: </span><span class='hs-definition'>listId</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
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

Next, lets write a function to `reverse` a list. Of course, we'd like to
verify that `reverse` doesn't leave any elements behind; that is that the 
output has the same set of values as the input list. This is somewhat more 
interesting because of the *tail recursive* helper `go`. Do you understand 
the type that is inferred for it? (Put your mouse over `go` to see the 
inferred type.)


<pre><span class=hs-linenum>249: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reverse</span>       <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-keyword'>| (SameElts v xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>250: </span><a class=annot href="#"><span class=annottext>forall a. xs:[a] -&gt; {VV : [a] | (listElts([VV]) = listElts([xs]))}</span><span class='hs-definition'>reverse</span></a>           <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (len([VV]) = 0)}
-&gt; x2:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([x1]);
                                          listElts([x2])])),
               (listElts([VV]) = Set_cup([listElts([x2]); listElts([x1])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (? Set_emp([listElts([VV])])),
                                           (len([VV]) = 0),
                                           (len([VV]) &gt;= 0)}</span><span class='hs-conid'>[]</span></a> 
<span class=hs-linenum>251: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>252: </span>    <a class=annot href="#"><span class=annottext>acc:{VV : [a] | (len([VV]) &gt;= 0)}
-&gt; x1:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([acc]);
                                          listElts([x1])])),
               (listElts([VV]) = Set_cup([listElts([x1]); listElts([acc])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>acc</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = acc),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>acc</span></a>
<span class=hs-linenum>253: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>acc</span> <span class='hs-layout'>(</span><span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>ys</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>acc:{VV : [a] | (len([VV]) &gt;= 0)}
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


<pre><span class=hs-linenum>263: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>append</span>       <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (UnionElts v xs ys) }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>264: </span><a class=annot href="#"><span class=annottext>forall a.
x1:[a]
-&gt; ys:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([x1]);
                                          listElts([ys])])),
               (listElts([VV]) = Set_cup([listElts([ys]); listElts([x1])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-definition'>append</span></a> <span class='hs-conid'>[]</span>     <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>ys</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
<span class=hs-linenum>265: </span><span class='hs-definition'>append</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varid'>ys</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
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

Lets round off the list trilogy, with `filter`. Here, we can verify
that it returns a **subset of** the values of the input list.


<pre><span class=hs-linenum>275: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>filter</span>      <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-keyword'>| (SubElts v xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>276: </span>
<span class=hs-linenum>277: </span><a class=annot href="#"><span class=annottext>forall a.
(a -&gt; (GHC.Types.Bool))
-&gt; x2:[a]
-&gt; {VV : [a] | (? Set_sub([listElts([VV]); listElts([x2])])),
               (listElts([x2]) = Set_cup([listElts([x2]); listElts([VV])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-definition'>filter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>f</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
{VV : [{VV : a | false}]&lt;p&gt; | (? Set_emp([listElts([VV])])),
                              (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>278: </span><span class='hs-definition'>filter</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>279: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p y&gt;]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (len([VV]) = (1 + len([ys]))),
                  (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
(a -&gt; (GHC.Types.Bool))
-&gt; x2:[a]
-&gt; {VV : [a] | (? Set_sub([listElts([VV]); listElts([x2])])),
               (listElts([x2]) = Set_cup([listElts([x2]); listElts([VV])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> 
<span class=hs-linenum>280: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
(a -&gt; (GHC.Types.Bool))
-&gt; x2:[a]
-&gt; {VV : [a] | (? Set_sub([listElts([VV]); listElts([x2])])),
               (listElts([x2]) = Set_cup([listElts([x2]); listElts([VV])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

Merge Sort
==========

Lets conclude this entry with one larger example: `mergeSort`. 
We'd like to verify that, well, the list that is returned 
contains the same set of elements as the input list. 

And so we will!

But first, lets remind ourselves of how `mergeSort` works

1. `split` the input list into two halves, 
2. `sort`  each half, recursively, 
3. `merge` the sorted halves to obtain the sorted list.


Split
-----

We can `split` a list into two, roughly equal parts like so:


<pre><span class=hs-linenum>305: </span><a class=annot href="#"><span class=annottext>forall a.
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
<span class=hs-linenum>306: </span><span class='hs-definition'>split</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a -&gt; b -&gt; Bool&gt;. x1:a -&gt; b&lt;p2 x1&gt; -&gt; (a , b)&lt;p2&gt;</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
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
<span class=hs-linenum>307: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>308: </span>    <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (? Set_sub([listElts([VV]); listElts([xs])])),
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

LiquidHaskell verifies that the relevant property of `split` is


<pre><span class=hs-linenum>314: </span><span class='hs-keyword'>{-@</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>ys</span> <span class='hs-varid'>zs</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>UnionElts</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>ys</span> <span class='hs-varid'>zs</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>@-}</span>
</pre>

The funny syntax with angle brackets simply says that the output is a 
a *pair* `(ys, zs)` whose union is the list of elements of the input.

(**Aside** yes, this is indeed a dependent tuple; we will revisit tuples
later to understand whats going on with the odd syntax.)

Merge
-----

Dually, we `merge` two (sorted) lists like so:


<pre><span class=hs-linenum>329: </span><a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
xs:[a]
-&gt; x1:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([x1]);
                                          listElts([xs])])),
               (listElts([VV]) = Set_cup([listElts([xs]); listElts([x1])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-definition'>merge</span></a> <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>xs</span></a> <span class='hs-conid'>[]</span>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>330: </span><span class='hs-definition'>merge</span> <span class='hs-conid'>[]</span> <span class='hs-varid'>ys</span>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
<span class=hs-linenum>331: </span><span class='hs-definition'>merge</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>yozz</span><span class='hs-conop'>:</span><span class='hs-varid'>ys</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>332: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:a
-&gt; y:a -&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = yozz)}</span><span class='hs-varid'>yozz</span></a>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
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
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>merge</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = yozz)}</span><span class='hs-varid'>yozz</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p y&gt;]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (len([VV]) = (1 + len([ys]))),
                  (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>333: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = yozz)}</span><span class='hs-varid'>yozz</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
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
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>merge</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p y&gt;]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (len([VV]) = (1 + len([ys]))),
                  (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
</pre>

As you might expect, the elements of the returned list are the union of the
elements of the input, or as LiquidHaskell might say,


<pre><span class=hs-linenum>340: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>merge</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (UnionElts v x y)}</span> <span class='hs-keyword'>@-}</span>
</pre>

Sort
----

Finally, we put all the pieces together by


<pre><span class=hs-linenum>349: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>mergeSort</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (SameElts v xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>350: </span><a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
x1:[a]
-&gt; {VV : [a] | (listElts([VV]) = Set_cup([listElts([x1]);
                                          listElts([x1])])),
               (listElts([VV]) = listElts([x1])),
               (listElts([x1]) = Set_cup([listElts([x1]); listElts([VV])]))}</span><span class='hs-definition'>mergeSort</span></a> <span class='hs-conid'>[]</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
{VV : [{VV : a | false}]&lt;p&gt; | (? Set_emp([listElts([VV])])),
                              (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>351: </span><span class='hs-definition'>mergeSort</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (? Set_emp([listElts([VV])])),
                                           (len([VV]) = 0),
                                           (len([VV]) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>352: </span><span class='hs-definition'>mergeSort</span> <span class='hs-varid'>xs</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:[a]
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
<span class=hs-linenum>353: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>354: </span>    <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),
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
