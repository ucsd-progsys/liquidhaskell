---
layout: post
title: Putting Things In Order
date: 2013-07-29 16:12
comments: true
tags:
   - abstract-refinements
author: Niki Vazou and Ranjit Jhala
published: true 
demo: Order.hs
---

Hello again! Since we last met, much has happened that
we're rather excited about, and which we promise to get
to in the fullness of time.

Today, however, lets continue with our exploration of
abstract refinements. We'll see that this rather innocent 
looking mechanism packs quite a punch, by showing how 
it can encode various **ordering** properties of 
recursive data structures.

<!-- more -->

<pre><span class=hs-linenum>26: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>PuttingThingsInOrder</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>27: </span>
<span class=hs-linenum>28: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>break</span><span class='hs-layout'>)</span>
<span class=hs-linenum>29: </span>
<span class=hs-linenum>30: </span><span class='hs-comment'>-- Haskell Type Definitions</span>
<span class=hs-linenum>31: </span><span class='hs-definition'>plusOnes</span>                         <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-conid'>Int</span><span class='hs-layout'>,</span> <span class='hs-conid'>Int</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>32: </span><span class='hs-definition'>insertSort</span><span class='hs-layout'>,</span> <span class='hs-varid'>mergeSort</span><span class='hs-layout'>,</span> <span class='hs-varid'>quickSort</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
</pre>

Abstract Refinements
--------------------

 Recall that *abstract refinements* are a mechanism that let us write and check types of the form
<pre><span class=hs-linenum>36: </span><span class='hs-definition'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span>
</pre>

which states that the output of `maxInt` preserves 
*whatever* invariants held for its two inputs as 
long as both those inputs *also* satisfied those 
invariants. 

First, lets see how we can (and why we may want to) 
abstractly refine data types. 

Polymorphic Association Lists
-----------------------------

Suppose, we require a type for association lists. 
Lets define one that is polymorphic over keys `k` 
and values `v` 


<pre><span class=hs-linenum>55: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>AssocP</span> <span class='hs-varid'>k</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>KVP</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-varid'>k</span><span class='hs-layout'>,</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span>
</pre>

Now, in a program, you might have multiple association
lists, whose keys satisfy different properties. 
For example, we might have a table for mapping digits 
to the corresponding English string


<pre><span class=hs-linenum>64: </span><span class='hs-definition'>digitsP</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>AssocP</span> <span class='hs-conid'>Int</span> <span class='hs-conid'>String</span>
<span class=hs-linenum>65: </span><a class=annot href="#"><span class=annottext>(PuttingThingsInOrder.AssocP {VV : (GHC.Types.Int) | (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)} [(GHC.Types.Char)])</span><span class='hs-definition'>digitsP</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)}, {VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)})]
-&gt; (PuttingThingsInOrder.AssocP {VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)} {VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)})</span><span class='hs-conid'>KVP</span></a> <span class='hs-keyglyph'>[</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV == 1) &amp;&amp; (VV &gt; 0)}, {VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)})&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt;</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"one"</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>66: </span>              <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)}, {VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)})&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt;</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (2  :  int))}</span><span class='hs-num'>2</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"two"</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>67: </span>              <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)}, {VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)})&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt;</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (3  :  int))}</span><span class='hs-num'>3</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"three"</span></a><span class='hs-layout'>)</span> <span class='hs-keyglyph'>]</span>
</pre>

We could have a separate table for *sparsely* storing 
the contents of an array of size `1000`.


<pre><span class=hs-linenum>74: </span><span class='hs-definition'>sparseVecP</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>AssocP</span> <span class='hs-conid'>Int</span> <span class='hs-conid'>Double</span>
<span class=hs-linenum>75: </span><a class=annot href="#"><span class=annottext>(PuttingThingsInOrder.AssocP {VV : (GHC.Types.Int) | (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)} (GHC.Types.Double))</span><span class='hs-definition'>sparseVecP</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)}, (GHC.Types.Double))]
-&gt; (PuttingThingsInOrder.AssocP {VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)} (GHC.Types.Double))</span><span class='hs-conid'>KVP</span></a> <span class='hs-keyglyph'>[</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)}, (GHC.Types.Double))</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (12  :  int))}</span><span class='hs-num'>12</span></a> <span class='hs-layout'>,</span>  <a class=annot href="#"><span class=annottext>(GHC.Types.Double)</span><span class='hs-num'>34.1</span></a> <span class='hs-layout'>)</span>
<span class=hs-linenum>76: </span>                 <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)}, (GHC.Types.Double))</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (92  :  int))}</span><span class='hs-num'>92</span></a> <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>(GHC.Types.Double)</span><span class='hs-num'>902.83</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>77: </span>                 <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)}, (GHC.Types.Double))</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (451  :  int))}</span><span class='hs-num'>451</span></a><span class='hs-layout'>,</span>   <a class=annot href="#"><span class=annottext>(GHC.Types.Double)</span><span class='hs-num'>2.95</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>78: </span>                 <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)}, (GHC.Types.Double))</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (877  :  int))}</span><span class='hs-num'>877</span></a><span class='hs-layout'>,</span>   <a class=annot href="#"><span class=annottext>(GHC.Types.Double)</span><span class='hs-num'>3.1</span></a> <span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span>
</pre>

The **keys** used in the two tables have rather 
different properties, which we may want to track 
at compile time.

- In `digitsP` the keys are between `0` and `9` 
- In `sparseVecP` the keys are between `0` and `999`. 

Well, since we had the foresight to parameterize 
the key type in `AssocP`, we can express the above 
properties by appropriately **instantiating** the type
of `k` with refined versions


<pre><span class=hs-linenum>94: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>digitsP</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>AssocP</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| (Btwn 0 v 9)}</span> <span class='hs-conid'>String</span> <span class='hs-keyword'>@-}</span>
</pre>

and 


<pre><span class=hs-linenum>100: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>sparseVecP</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>AssocP</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| (Btwn 0 v 1000)}</span> <span class='hs-conid'>Double</span> <span class='hs-keyword'>@-}</span>
</pre>

where `Btwn` is just an alias 


<pre><span class=hs-linenum>106: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>Btwn</span> <span class='hs-conid'>Lo</span> <span class='hs-conid'>V</span> <span class='hs-conid'>Hi</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Lo</span> <span class='hs-varop'>&lt;=</span> <span class='hs-conid'>V</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-conid'>V</span> <span class='hs-varop'>&lt;=</span> <span class='hs-conid'>Hi</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>

Monomorphic Association Lists
-----------------------------

Now, suppose that for one reason or another, we want to 
specialize our association list so that the keys are of 
type `Int`. 


<pre><span class=hs-linenum>117: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>Assoc</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>KV</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-conid'>Int</span><span class='hs-layout'>,</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span>
</pre>

(We'd probably also want to exploit the `Int`-ness 
in the implementation but thats a tale for another day.)

Now, we have our two tables


<pre><span class=hs-linenum>126: </span><span class='hs-definition'>digits</span>    <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Assoc</span> <span class='hs-conid'>String</span>
<span class=hs-linenum>127: </span><a class=annot href="#"><span class=annottext>(PuttingThingsInOrder.Assoc [(GHC.Types.Char)])</span><span class='hs-definition'>digits</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; Bool&gt;.
[({VV : (GHC.Types.Int)&lt;p&gt; | true}, {VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)})]
-&gt; (PuttingThingsInOrder.Assoc &lt;p&gt; {VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)})</span><span class='hs-conid'>KV</span></a> <span class='hs-keyglyph'>[</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV == 1) &amp;&amp; (VV &gt; 0)}, {VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)})&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt;</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"one"</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>128: </span>               <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)}, {VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)})&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt;</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (2  :  int))}</span><span class='hs-num'>2</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"two"</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>129: </span>               <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)}, {VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)})&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt;</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (3  :  int))}</span><span class='hs-num'>3</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"three"</span></a><span class='hs-layout'>)</span> <span class='hs-keyglyph'>]</span>
<span class=hs-linenum>130: </span>
<span class=hs-linenum>131: </span><span class='hs-definition'>sparseVec</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Assoc</span> <span class='hs-conid'>Double</span>
<span class=hs-linenum>132: </span><a class=annot href="#"><span class=annottext>(PuttingThingsInOrder.Assoc (GHC.Types.Double))</span><span class='hs-definition'>sparseVec</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; Bool&gt;.
[({VV : (GHC.Types.Int)&lt;p&gt; | true}, (GHC.Types.Double))]
-&gt; (PuttingThingsInOrder.Assoc &lt;p&gt; (GHC.Types.Double))</span><span class='hs-conid'>KV</span></a> <span class='hs-keyglyph'>[</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)}, (GHC.Types.Double))</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (12  :  int))}</span><span class='hs-num'>12</span></a> <span class='hs-layout'>,</span>  <a class=annot href="#"><span class=annottext>(GHC.Types.Double)</span><span class='hs-num'>34.1</span></a> <span class='hs-layout'>)</span>
<span class=hs-linenum>133: </span>               <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)}, (GHC.Types.Double))</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (92  :  int))}</span><span class='hs-num'>92</span></a> <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>(GHC.Types.Double)</span><span class='hs-num'>902.83</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>134: </span>               <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)}, (GHC.Types.Double))</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (451  :  int))}</span><span class='hs-num'>451</span></a><span class='hs-layout'>,</span>   <a class=annot href="#"><span class=annottext>(GHC.Types.Double)</span><span class='hs-num'>2.95</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>135: </span>               <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)}, (GHC.Types.Double))</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (877  :  int))}</span><span class='hs-num'>877</span></a><span class='hs-layout'>,</span>   <a class=annot href="#"><span class=annottext>(GHC.Types.Double)</span><span class='hs-num'>3.1</span></a> <span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span>
</pre>

but since we didn't make the key type generic, it seems 
we have no way to distinguish between the invariants of 
the two sets of keys. Bummer!

Abstractly Refined Data
-----------------------

We *could* define *two separate* types of association 
lists that capture different invariants, but frankly, 
thats rather unfortunate, as we'd then have to 
duplicate the code the manipulates the structures. 
Of course, we'd like to have (type) systems help 
keep an eye on different invariants, but we'd 
*really* rather not have to duplicate code to 
achieve that end. Thats the sort of thing that
drives a person to JavaScript ;-).

Fortunately, all is not lost. 

If you were paying attention [last time][blog-absref] 
then you'd realize that this is the perfect job for 
an abstract refinement, this time applied to a `data` 
definition:


<pre><span class=hs-linenum>163: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>Assoc</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>164: </span>      <span class='hs-keyglyph'>=</span> <span class='hs-conid'>KV</span> <span class='hs-layout'>(</span><span class='hs-varid'>z</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>,</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span> 
</pre>

The definition refines the type for `Assoc` to introduce
an abstract refinement `p` which is, informally speaking,
a property of `Int`. The definition states that each `Int`
in the association list in fact satisfies `p` as, `Int<p>`
is an abbreviation for `{v:Int| (p v)}`.

Now, we can *have* our `Int` keys and *refine* them too!
For example, we can write:


<pre><span class=hs-linenum>177: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>digits</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Assoc</span> <span class='hs-layout'>(</span><span class='hs-conid'>String</span><span class='hs-layout'>)</span> <span class='hs-keyword'>&lt;{\v -&gt; (Btwn 0 v 9)}&gt;</span> <span class='hs-keyword'>@-}</span>
</pre>

to track the invariant for the `digits` map, and write


<pre><span class=hs-linenum>183: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>sparseVec</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Assoc</span> <span class='hs-conid'>Double</span> <span class='hs-keyword'>&lt;{\v -&gt; (Btwn 0 v 1000)}&gt;</span> <span class='hs-keyword'>@-}</span>
</pre>

Thus, we can recover (some of) the benefits of abstracting 
over the type of the key by instead parameterizing the type
directly over the possible invariants. We will have much 
[more to say][blog-absref-vec] on association lists 
(or more generally, finite maps) and abstract refinements, 
but lets move on for the moment.

Dependent Tuples
----------------

It is no accident that we have reused Haskell's function 
type syntax to define abstract refinements (`p :: Int -> Prop`);
interesting things start to happen if we use multiple parameters.

Consider the function `break` from the Prelude. 


<pre><span class=hs-linenum>203: </span><span class='hs-definition'>break</span>                   <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-layout'>,</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-layout'>)</span>
<span class=hs-linenum>204: </span><a class=annot href="#"><span class=annottext>forall a.
(a -&gt; (GHC.Types.Bool))
-&gt; x:[a] -&gt; ([a], [a])&lt;\y VV -&gt; ((len x) == ((len y) + (len VV)))&gt;</span><span class='hs-definition'>break</span></a> <span class='hs-keyword'>_</span> <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>xs</span></a><span class='hs-keyglyph'>@</span><span class='hs-conid'>[]</span>           <span class='hs-keyglyph'>=</span>  <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a-&gt; b-&gt; Bool&gt;.
a:a
-&gt; b:{VV : b&lt;p2 a&gt; | true}
-&gt; {VV : (a, b)&lt;p2&gt; | ((fst VV) == a) &amp;&amp; ((snd VV) == b)}</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (((null VV)) &lt;=&gt; true) &amp;&amp; (VV == xs) &amp;&amp; (VV == (GHC.Types.[])) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (((null VV)) &lt;=&gt; true) &amp;&amp; (VV == xs) &amp;&amp; (VV == (GHC.Types.[])) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>205: </span><span class='hs-definition'>break</span> <span class='hs-varid'>p</span> <span class='hs-varid'>xs</span><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs'</span><span class='hs-layout'>)</span>
<span class=hs-linenum>206: </span>           <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>p</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a>        <span class='hs-keyglyph'>=</span>  <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a-&gt; b-&gt; Bool&gt;.
a:a
-&gt; b:{VV : b&lt;p2 a&gt; | true}
-&gt; {VV : (a, b)&lt;p2&gt; | ((fst VV) == a) &amp;&amp; ((snd VV) == b)}</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; true) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-conid'>[]</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>207: </span>           <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>  <span class='hs-keyglyph'>=</span>  <span class='hs-keyword'>let</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV == ys) &amp;&amp; ((len VV) == (len ys)) &amp;&amp; ((len xs') == ((len zs) + (len VV))) &amp;&amp; (VV /= xs) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt; (len xs)) &amp;&amp; ((len VV) &lt;= (len xs'))}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == zs) &amp;&amp; ((len VV) == (len zs)) &amp;&amp; ((len xs') == ((len ys) + (len VV))) &amp;&amp; ((len xs') == ((len ys) + (len VV))) &amp;&amp; (VV /= xs) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt; (len xs)) &amp;&amp; ((len VV) &lt;= (len xs'))}</span><span class='hs-varid'>zs</span></a><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(a -&gt; (GHC.Types.Bool))
-&gt; x:[a] -&gt; ([a], [a])&lt;\y VV -&gt; ((len x) == ((len y) + (len VV)))&gt;</span><span class='hs-varid'>break</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>p</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs') &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs'</span></a> 
<span class=hs-linenum>208: </span>                           <span class='hs-keyword'>in</span> <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a-&gt; b-&gt; Bool&gt;.
a:a
-&gt; b:{VV : b&lt;p2 a&gt; | true}
-&gt; {VV : (a, b)&lt;p2&gt; | ((fst VV) == a) &amp;&amp; ((snd VV) == b)}</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:a
-&gt; xs:[{VV : a&lt;p x&gt; | true}]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (VV == ys) &amp;&amp; (VV == ys) &amp;&amp; ((len VV) == (len ys)) &amp;&amp; ((len xs') == ((len zs) + (len VV))) &amp;&amp; (VV /= xs) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt; (len xs)) &amp;&amp; ((len VV) &lt;= (len xs'))}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV == zs) &amp;&amp; (VV == zs) &amp;&amp; ((len VV) == (len zs)) &amp;&amp; ((len xs') == ((len ys) + (len VV))) &amp;&amp; ((len xs') == ((len ys) + (len VV))) &amp;&amp; (VV /= xs) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt; (len xs)) &amp;&amp; ((len VV) &lt;= (len xs'))}</span><span class='hs-varid'>zs</span></a><span class='hs-layout'>)</span>
</pre>

From the comments in [Data.List][data-list], `break p xs`: 
"returns a tuple where the first element is longest prefix (possibly empty)
`xs` of elements that do not satisfy `p` and second element is the 
remainder of the list."

We could formalize the notion of the *second-element-being-the-remainder* 
using sizes. That is, we'd like to specify that the length of the second 
element equals the length of `xs` minus the length of the first element.  
That is, we need a way to allow the refinement of the second element to 
*depend on* the value in the first refinement.
Again, we could define a special kind of tuple-of-lists-type that 
has the above property *baked in*, but thats just not how we roll.

 Instead, lets use abstract refinements to give us **dependent tuples**
<pre><span class=hs-linenum>225: </span><span class='hs-keyword'>data</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span><span class='hs-layout'>,</span><span class='hs-varid'>b</span><span class='hs-layout'>)</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span><span class='hs-layout'>,</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>x</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> 
</pre>

Here, the abstract refinement takes two parameters, 
an `a` and a `b`. In the body of the tuple, the 
first element is named `x` and we specify that 
the second element satisfies the refinement `p x`, 
i.e. a partial application of `p` with the first element. 
In other words, the second element is a value of type
`{v:b | (p x v)}`.

As before, we can instantiate the `p` in *different* ways. 
For example the whimsical


<pre><span class=hs-linenum>240: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>plusOnes</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-conid'>Int</span><span class='hs-layout'>,</span> <span class='hs-conid'>Int</span><span class='hs-layout'>)</span><span class='hs-keyword'>&lt;{\x1 x2 -&gt; x2 = x1 + 1}&gt;</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>241: </span><a class=annot href="#"><span class=annottext>[((GHC.Types.Int), (GHC.Types.Int))&lt;\x1 VV -&gt; (VV == (x1 + 1))&gt;]</span><span class='hs-definition'>plusOnes</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)}, {VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)})&lt;\x3 VV -&gt; (VV == (x3 + 1)) &amp;&amp; (VV &gt; 0) &amp;&amp; (VV &gt; x3) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)&gt;]&lt;\x1 VV -&gt; (VV /= x1)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV == 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)}, {VV : (GHC.Types.Int) | (VV == 1) &amp;&amp; (VV &gt; 0)})&lt;\x2 VV -&gt; (VV == 1) &amp;&amp; (VV == (x2 + 1)) &amp;&amp; (VV &gt; 0) &amp;&amp; (VV &gt; x2)&gt;</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (0  :  int))}</span><span class='hs-num'>0</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)}, {VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)})&lt;\x2 VV -&gt; (VV == (x2 + 1)) &amp;&amp; (VV &gt; 0) &amp;&amp; (VV &gt; x2) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)&gt;</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (5  :  int))}</span><span class='hs-num'>5</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (6  :  int))}</span><span class='hs-num'>6</span></a><span class='hs-layout'>)</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)}, {VV : (GHC.Types.Int) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)})&lt;\x2 VV -&gt; (VV == (x2 + 1)) &amp;&amp; (VV &gt; 0) &amp;&amp; (VV &gt; x2) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 1000)&gt;</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (999  :  int))}</span><span class='hs-num'>999</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (1000  :  int))}</span><span class='hs-num'>1000</span></a><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span>
</pre>

and returning to the *remainder* property for  `break` 


<pre><span class=hs-linenum>247: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>break</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> 
<span class=hs-linenum>248: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-layout'>,</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-layout'>)</span><span class='hs-keyword'>&lt;{\y z -&gt; (Break x y z)}&gt;</span> <span class='hs-keyword'>@-}</span>
</pre>

using the predicate alias


<pre><span class=hs-linenum>254: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>Break</span> <span class='hs-conid'>X</span> <span class='hs-conid'>Y</span> <span class='hs-conid'>Z</span>   <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-conid'>Y</span><span class='hs-layout'>)</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-conid'>Z</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>


Abstractly Refined Lists
------------------------

Right, we've been going on for a bit. Time to put things *in order*.

To recap: we've already seen one way to abstractly refine lists: 
to recover a *generic* means of refining a *monomorphic* list 
(e.g. the list of `Int` keys.) However, in that case we were 
talking about *individual* keys.
Next, we build upon the dependent-tuples technique we just 
saw to use abstract refinements to relate *different* 
elements inside containers.

In particular, we can use them to specify that *every pair* 
of elements inside the list is related according to some 
abstract relation `p`. By *instantiating* `p` appropriately,
we will be able to recover various forms of (dis) order. 

 Consider the refined definition of good old Haskell lists:
<pre><span class=hs-linenum>277: </span><span class='hs-keyword'>data</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>278: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-conid'>[]</span>  <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span>
<span class=hs-linenum>279: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conop'>:</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>h</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>h</span><span class='hs-varop'>&gt;</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span>
</pre>

Whoa! Thats a bit of a mouthful. Lets break it down.

* The type is parameterized with a refinement `p :: a -> a -> Prop` 
  Think of `p` as a *binary relation* over the `a` values comprising
  the list.

* The empty list `[]` is a `[]<p>`. Clearly, the empty list has no
  elements whatsoever and so every pair is trivially, or rather, 
  vacuously related by `p`.

* The cons constructor `(:)` takes a head `h` of type `a` and a tail
  of `a<p h>` values, each of which is *related to* `h` **and** which 
  (recursively) are pairwise related `[...]<p>` and returns a list where 
  *all* elements are pairwise related `[a]<p>`.

Pairwise Related
----------------

Note that we're being a bit sloppy when we say *pairwise* related.

 What we really mean is that if a list
<pre><span class=hs-linenum>303: </span><span class='hs-keyglyph'>[</span><span class='hs-varid'>x1</span><span class='hs-layout'>,</span><span class='hs-varop'>...</span><span class='hs-layout'>,</span><span class='hs-varid'>xn</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span>
</pre>

then for each `1 <= i < j <= n` we have `(p xi xj)`.

 To see why, consider the list
<pre><span class=hs-linenum>309: </span><span class='hs-keyglyph'>[</span><span class='hs-varid'>x1</span><span class='hs-layout'>,</span> <span class='hs-varid'>x2</span><span class='hs-layout'>,</span> <span class='hs-varid'>x3</span><span class='hs-layout'>,</span> <span class='hs-varop'>...</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span>
</pre>

 This list unfolds into a head and tail 
<pre><span class=hs-linenum>313: </span><span class='hs-definition'>x1</span>                <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>314: </span><span class='hs-keyglyph'>[</span><span class='hs-varid'>x2</span><span class='hs-layout'>,</span> <span class='hs-varid'>x3</span><span class='hs-layout'>,</span><span class='hs-varop'>...</span><span class='hs-keyglyph'>]</span>      <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>x1</span><span class='hs-varop'>&gt;</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span>
</pre>

 The above tail unfolds into
<pre><span class=hs-linenum>318: </span><span class='hs-definition'>x2</span>                <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>x1</span><span class='hs-varop'>&gt;</span>
<span class=hs-linenum>319: </span><span class='hs-keyglyph'>[</span><span class='hs-varid'>x3</span><span class='hs-layout'>,</span> <span class='hs-varop'>...</span><span class='hs-keyglyph'>]</span>         <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>x1</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>p</span> <span class='hs-varid'>x2</span><span class='hs-varop'>&gt;</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span>
</pre>

 And finally into 
<pre><span class=hs-linenum>323: </span><span class='hs-definition'>x3</span>                <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>x1</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>p</span> <span class='hs-varid'>x2</span><span class='hs-varop'>&gt;</span>
<span class=hs-linenum>324: </span><span class='hs-keyglyph'>[</span><span class='hs-varop'>...</span><span class='hs-keyglyph'>]</span>             <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>x1</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>p</span> <span class='hs-varid'>x2</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>p</span> <span class='hs-varid'>x3</span><span class='hs-varop'>&gt;</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span>
</pre>

That is, each element `xj` satisfies the refinement 
`(p xi xj)` for each `i < j`.

Using Abstractly Refined Lists
------------------------------

Urgh. *Math is hard!*  

Lets see how we can *program* with these funnily refined lists.

For starters, we can define a few helpful type aliases.


<pre><span class=hs-linenum>340: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>xi</span> <span class='hs-varid'>xj</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xi</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>xj</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>@-}</span>      
<span class=hs-linenum>341: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>DecrList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>xi</span> <span class='hs-varid'>xj</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xi</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>xj</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>342: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>UniqList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>xi</span> <span class='hs-varid'>xj</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xi</span> <span class='hs-varop'>/=</span> <span class='hs-varid'>xj</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>@-}</span>
</pre>

As you might expect, an `IncrList` is a list of values in *increasing* order:


<pre><span class=hs-linenum>348: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>whatGosUp</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>IncrList</span> <span class='hs-conid'>Integer</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>349: </span><a class=annot href="#"><span class=annottext>[(GHC.Integer.Type.Integer)]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-definition'>whatGosUp</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : (GHC.Integer.Type.Integer) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)}]&lt;\x2 VV -&gt; (VV == (x2 + 1)) &amp;&amp; (VV &gt; 0) &amp;&amp; (VV &gt; x2) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><span class='hs-num'>1</span><span class='hs-layout'>,</span><span class='hs-num'>2</span><span class='hs-layout'>,</span><span class='hs-num'>3</span><span class='hs-keyglyph'>]</span>
</pre>

Similarly, a `DecrList` contains its values in *decreasing* order:


<pre><span class=hs-linenum>355: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>mustGoDown</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>DecrList</span> <span class='hs-conid'>Integer</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>356: </span><a class=annot href="#"><span class=annottext>[(GHC.Integer.Type.Integer)]&lt;\xi VV -&gt; (xi &gt;= VV)&gt;</span><span class='hs-definition'>mustGoDown</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : (GHC.Integer.Type.Integer) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)}]&lt;\x3 VV -&gt; (VV == 1) &amp;&amp; (x3 /= VV) &amp;&amp; (VV &gt; 0) &amp;&amp; (x3 &gt;= VV) &amp;&amp; (VV &lt; x3)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><span class='hs-num'>3</span><span class='hs-layout'>,</span><span class='hs-num'>2</span><span class='hs-layout'>,</span><span class='hs-num'>1</span><span class='hs-keyglyph'>]</span>
</pre>

My personal favorite though, is a `UniqList` which has *no duplicates*:


<pre><span class=hs-linenum>362: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>noDuplicates</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>UniqList</span> <span class='hs-conid'>Integer</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>363: </span><a class=annot href="#"><span class=annottext>[(GHC.Integer.Type.Integer)]&lt;\xi VV -&gt; (xi /= VV)&gt;</span><span class='hs-definition'>noDuplicates</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : (GHC.Integer.Type.Integer) | (VV &gt; 0) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)}]&lt;\x3 VV -&gt; (x3 /= VV) &amp;&amp; (VV &gt; 0) &amp;&amp; (x3 &gt;= VV) &amp;&amp; (VV &lt; x3) &amp;&amp; (0 &lt;= VV) &amp;&amp; (VV &lt;= 9)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><span class='hs-num'>1</span><span class='hs-layout'>,</span><span class='hs-num'>3</span><span class='hs-layout'>,</span><span class='hs-num'>2</span><span class='hs-keyglyph'>]</span>
</pre>

Sorting Lists
-------------

Its all very well to *specify* lists with various kinds of invariants. 
The question is, how easy is it to *establish* these invariants?

Lets find out, by turning inevitably to that staple of all forms of
formal verification: your usual textbook sorting procedures.

**Insertion Sort**

First up: insertion sort. Well, no surprises here:


<pre><span class=hs-linenum>380: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>insertSort</span>    <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>381: </span><a class=annot href="#"><span class=annottext>forall a. (GHC.Classes.Ord a) =&gt; [a] -&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-definition'>insertSort</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
{VV : [{VV : a | false}]&lt;p&gt; | (((null VV)) &lt;=&gt; true) &amp;&amp; ((len VV) == 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>382: </span><span class='hs-definition'>insertSort</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a -&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt; -&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-varid'>insert</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>[a] -&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-varid'>insertSort</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span> 
</pre>

The hard work is done by `insert` which places an 
element into the correct position of a sorted list


<pre><span class=hs-linenum>389: </span><a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
a
-&gt; x1:[a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt;
-&gt; {VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV /= x1) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len x1))}</span><span class='hs-definition'>insert</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>y</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; true) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>390: </span><span class='hs-definition'>insert</span> <span class='hs-varid'>y</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>391: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : (GHC.Types.Bool) | (((Prop VV)) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:{VV : a | (VV &gt;= y)}
-&gt; xs:[{VV : a&lt;p x&gt; | (VV &gt;= y)}]&lt;p&gt;
-&gt; {VV : [{VV : a | (VV &gt;= y)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:{VV : a | (VV &gt;= x) &amp;&amp; (VV &gt;= y)}
-&gt; xs:[{VV : a&lt;p x&gt; | (VV &gt;= x) &amp;&amp; (VV &gt;= y)}]&lt;p&gt;
-&gt; {VV : [{VV : a | (VV &gt;= x) &amp;&amp; (VV &gt;= y)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= x)}]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> 
<span class=hs-linenum>392: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:{VV : a | (VV &gt;= x)}
-&gt; xs:[{VV : a&lt;p x&gt; | (VV &gt;= x)}]&lt;p&gt;
-&gt; {VV : [{VV : a | (VV &gt;= x)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
a
-&gt; x1:[a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt;
-&gt; {VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV /= x1) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len x1))}</span><span class='hs-varid'>insert</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= x)}]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

LiquidHaskell infers that if you give `insert` an element 
and a sorted list, it returns a sorted list.


<pre><span class=hs-linenum>399: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>insert</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
</pre>

If you prefer the more Haskelly way of writing insertion sort, 
i.e. with a `foldr`, that works too. Can you figure out why?


<pre><span class=hs-linenum>406: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>insertSort'</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>407: </span><a class=annot href="#"><span class=annottext>forall a. (GHC.Classes.Ord a) =&gt; [a] -&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-definition'>insertSort'</span></a> <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>xs</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(a -&gt; [a]&lt;\x4 VV -&gt; (VV &gt;= x4)&gt; -&gt; [a]&lt;\x4 VV -&gt; (VV &gt;= x4)&gt;)
-&gt; [a]&lt;\x4 VV -&gt; (VV &gt;= x4)&gt; -&gt; [a] -&gt; [a]&lt;\x4 VV -&gt; (VV &gt;= x4)&gt;</span><span class='hs-varid'>foldr</span></a> <a class=annot href="#"><span class=annottext>a -&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt; -&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-varid'>insert</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; true) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-conid'>[]</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

**Merge Sort**

Well, you know the song goes. First, we write a function 
that **splits** the input into two parts:


<pre><span class=hs-linenum>416: </span><span class='hs-definition'>split</span>          <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-layout'>,</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-layout'>)</span>
<span class=hs-linenum>417: </span><a class=annot href="#"><span class=annottext>forall a.
x1:{VV : [a] | ((len VV) &gt;= 0)}
-&gt; ({VV : [a] | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))}, {VV : [a] | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))})&lt;\x2 VV -&gt; ((len x1) == ((len x2) + (len VV))) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1)) &amp;&amp; ((len VV) &lt;= (len x2))&gt;</span><span class='hs-definition'>split</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>zs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a-&gt; b-&gt; Bool&gt;.
a:a
-&gt; b:{VV : b&lt;p2 a&gt; | true}
-&gt; {VV : (a, b)&lt;p2&gt; | ((fst VV) == a) &amp;&amp; ((snd VV) == b)}</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:a
-&gt; xs:[{VV : a&lt;p x&gt; | true}]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; (VV == xs) &amp;&amp; ((len VV) == (len xs)) &amp;&amp; ((len zs) == ((len ys) + (len VV))) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &gt;= (len ys)) &amp;&amp; ((len VV) &lt;= (len zs))}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:a
-&gt; xs:[{VV : a&lt;p x&gt; | true}]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (VV == ys) &amp;&amp; (VV == ys) &amp;&amp; ((len VV) == (len ys)) &amp;&amp; ((len zs) == ((len xs) + (len VV))) &amp;&amp; ((len zs) == ((len xs) + (len VV))) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len xs)) &amp;&amp; ((len VV) &lt;= (len xs)) &amp;&amp; ((len VV) &lt;= (len zs))}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span> 
<span class=hs-linenum>418: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>419: </span>    <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; ((len VV) == (len xs)) &amp;&amp; ((len zs) == ((len ys) + (len VV))) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &gt;= (len ys)) &amp;&amp; ((len VV) &lt;= (len zs))}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == ys) &amp;&amp; ((len VV) == (len ys)) &amp;&amp; ((len zs) == ((len xs) + (len VV))) &amp;&amp; ((len zs) == ((len xs) + (len VV))) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len xs)) &amp;&amp; ((len VV) &lt;= (len xs)) &amp;&amp; ((len VV) &lt;= (len zs))}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
x1:{VV : [a] | ((len VV) &gt;= 0)}
-&gt; ({VV : [a] | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))}, {VV : [a] | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))})&lt;\x2 VV -&gt; ((len x1) == ((len x2) + (len VV))) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1)) &amp;&amp; ((len VV) &lt;= (len x2))&gt;</span><span class='hs-varid'>split</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == zs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>zs</span></a>
<span class=hs-linenum>420: </span><span class='hs-definition'>split</span> <span class='hs-varid'>xs</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a-&gt; b-&gt; Bool&gt;.
a:a
-&gt; b:{VV : b&lt;p2 a&gt; | true}
-&gt; {VV : (a, b)&lt;p2&gt; | ((fst VV) == a) &amp;&amp; ((snd VV) == b)}</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; true) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-conid'>[]</span></a><span class='hs-layout'>)</span>
</pre>

Then we need a function that **merges** two (sorted) lists


<pre><span class=hs-linenum>426: </span><a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
xs:[a]&lt;\x3 VV -&gt; (x3 &lt;= VV)&gt;
-&gt; x1:[a]&lt;\x2 VV -&gt; (x2 &lt;= VV)&gt;
-&gt; {VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &gt;= (len x1)) &amp;&amp; ((len VV) &gt;= (len xs))}</span><span class='hs-definition'>merge</span></a> <a class=annot href="#"><span class=annottext>[a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt;</span><span class='hs-varid'>xs</span></a> <span class='hs-conid'>[]</span>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>427: </span><span class='hs-definition'>merge</span> <span class='hs-conid'>[]</span> <span class='hs-varid'>ys</span>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
<span class=hs-linenum>428: </span><span class='hs-definition'>merge</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>ys</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>429: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : (GHC.Types.Bool) | (((Prop VV)) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a>          <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:{VV : a | (VV &gt;= x)}
-&gt; xs:[{VV : a&lt;p x&gt; | (VV &gt;= x)}]&lt;p&gt;
-&gt; {VV : [{VV : a | (VV &gt;= x)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
xs:[a]&lt;\x3 VV -&gt; (x3 &lt;= VV)&gt;
-&gt; x1:[a]&lt;\x2 VV -&gt; (x2 &lt;= VV)&gt;
-&gt; {VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &gt;= (len x1)) &amp;&amp; ((len VV) &gt;= (len xs))}</span><span class='hs-varid'>merge</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (x &lt;= VV)}]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:{VV : a | (VV &gt;= x) &amp;&amp; (VV &gt;= y)}
-&gt; xs:[{VV : a&lt;p x&gt; | (VV &gt;= x) &amp;&amp; (VV &gt;= y)}]&lt;p&gt;
-&gt; {VV : [{VV : a | (VV &gt;= x) &amp;&amp; (VV &gt;= y)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : a | (y &lt;= VV)}]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | (VV == ys) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>430: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:{VV : a | (VV &gt;= y)}
-&gt; xs:[{VV : a&lt;p x&gt; | (VV &gt;= y)}]&lt;p&gt;
-&gt; {VV : [{VV : a | (VV &gt;= y)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
xs:[a]&lt;\x3 VV -&gt; (x3 &lt;= VV)&gt;
-&gt; x1:[a]&lt;\x2 VV -&gt; (x2 &lt;= VV)&gt;
-&gt; {VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &gt;= (len x1)) &amp;&amp; ((len VV) &gt;= (len xs))}</span><span class='hs-varid'>merge</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:{VV : a | (VV &gt; y) &amp;&amp; (VV &gt;= x)}
-&gt; xs:[{VV : a&lt;p x&gt; | (VV &gt; y) &amp;&amp; (VV &gt;= x)}]&lt;p&gt;
-&gt; {VV : [{VV : a | (VV &gt; y) &amp;&amp; (VV &gt;= x)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : a | (x &lt;= VV)}]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (y &lt;= VV)}]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | (VV == ys) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
</pre>

LiquidHaskell deduces that if both inputs are 
ordered, then so is the output.


<pre><span class=hs-linenum>437: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>merge</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>438: </span>                     <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>439: </span>                     <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>440: </span>  <span class='hs-keyword'>@-}</span>
</pre>

Finally, using the above functions we write `mergeSort`:


<pre><span class=hs-linenum>446: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>mergeSort</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>447: </span><a class=annot href="#"><span class=annottext>forall a. (GHC.Classes.Ord a) =&gt; [a] -&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-definition'>mergeSort</span></a> <span class='hs-conid'>[]</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
{VV : [{VV : a | false}]&lt;p&gt; | (((null VV)) &lt;=&gt; true) &amp;&amp; ((len VV) == 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>448: </span><span class='hs-definition'>mergeSort</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; true) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>449: </span><span class='hs-definition'>mergeSort</span> <span class='hs-varid'>xs</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;
-&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt; -&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-varid'>merge</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>[a] -&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-varid'>mergeSort</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == ys) &amp;&amp; (VV == ys) &amp;&amp; ((len VV) == (len ys)) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &gt;= (len zs))}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>[a] -&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-varid'>mergeSort</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == zs) &amp;&amp; (VV == zs) &amp;&amp; ((len VV) == (len zs)) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len ys)) &amp;&amp; ((len VV) &lt;= (len ys))}</span><span class='hs-varid'>zs</span></a><span class='hs-layout'>)</span> 
<span class=hs-linenum>450: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>451: </span>    <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV == ys) &amp;&amp; ((len VV) == (len ys)) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt;= (len zs))}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == zs) &amp;&amp; ((len VV) == (len zs)) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len ys)) &amp;&amp; ((len VV) &lt;= (len ys))}</span><span class='hs-varid'>zs</span></a><span class='hs-layout'>)</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
x1:{VV : [a] | ((len VV) &gt;= 0)}
-&gt; ({VV : [a] | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))}, {VV : [a] | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))})&lt;\x2 VV -&gt; ((len x1) == ((len x2) + (len VV))) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1)) &amp;&amp; ((len VV) &lt;= (len x2))&gt;</span><span class='hs-varid'>split</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

Lets see how LiquidHaskell proves the output type. 

+ The first two cases are trivial: for an empty 
  or singleton list, we can vacuously instantiate 
  the abstract refinement with *any* concrete 
  refinement.

+ For the last case, we can inductively assume 
 `mergeSort ys` and `mergeSort zs` are sorted 
  lists, after which the type inferred for 
  `merge` kicks in, allowing LiquidHaskell to conclude
  that the output is also sorted.

**Quick Sort**

The previous two were remarkable because they were, well, quite *unremarkable*. 
Pretty much the standard textbook implementations work *as is*. 
Unlike the [classical][omega-sort] [developments][hasochism] 
using indexed types we don't have to define any auxiliary 
types for increasing lists, or lists whose value is in a 
particular range, or any specialized `cons` operators and 
so on.

With *quick sort* we need to do a tiny bit of work.


 We would like to define `quickSort` as
<pre><span class=hs-linenum>481: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>quickSort'</span>    <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>482: </span><span class='hs-definition'>quickSort'</span> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <span class='hs-conid'>[]</span>
<span class=hs-linenum>483: </span><span class='hs-definition'>quickSort'</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>lts</span> <span class='hs-varop'>++</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-conop'>:</span> <span class='hs-varid'>gts</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>484: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>485: </span>    <span class='hs-varid'>lts</span>           <span class='hs-keyglyph'>=</span> <span class='hs-varid'>quickSort'</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>y</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>y</span> <span class='hs-keyglyph'>&lt;-</span> <span class='hs-varid'>xs</span><span class='hs-layout'>,</span> <span class='hs-varid'>y</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>486: </span>    <span class='hs-varid'>gts</span>           <span class='hs-keyglyph'>=</span> <span class='hs-varid'>quickSort'</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>z</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>z</span> <span class='hs-keyglyph'>&lt;-</span> <span class='hs-varid'>xs</span><span class='hs-layout'>,</span> <span class='hs-varid'>z</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span>
</pre>

But, if you try it out, you'll see that LiquidHaskell 
*does not approve*. What could possibly be the trouble?

The problem lies with *append*. What type do we give `++`? 

 We might try something like
<pre><span class=hs-linenum>495: </span><span class='hs-layout'>(</span><span class='hs-varop'>++</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span>
</pre>

 but of course, this is bogus, as 
<pre><span class=hs-linenum>499: </span><span class='hs-keyglyph'>[</span><span class='hs-num'>1</span><span class='hs-layout'>,</span><span class='hs-num'>2</span><span class='hs-layout'>,</span><span class='hs-num'>4</span><span class='hs-keyglyph'>]</span> <span class='hs-varop'>++</span> <span class='hs-keyglyph'>[</span><span class='hs-num'>3</span><span class='hs-layout'>,</span><span class='hs-num'>5</span><span class='hs-layout'>,</span><span class='hs-num'>6</span><span class='hs-keyglyph'>]</span>
</pre>

is decidedly not an `IncrList`!

Instead, at this particular use of `++`, there is
an extra nugget of information: there is a *pivot*
element `x` such that every element in the first 
argument is less than `x` and every element in 
the second argument is greater than `x`. 

There is no way we can give the usual append `++` 
a type that reflects the above as there is no pivot 
`x` to refer to. Thus, with a heavy heart, we must
write a specialized pivot-append that uses this fact:


<pre><span class=hs-linenum>516: </span><a class=annot href="#"><span class=annottext>forall a.
piv:a
-&gt; x1:[{VV : a | (VV &lt; piv)}]&lt;\x3 VV -&gt; (VV &gt;= x3)&gt;
-&gt; ys:[{VV : a | (piv &lt;= VV)}]&lt;\x2 VV -&gt; (x2 &lt;= VV)&gt;
-&gt; {VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV /= x1) &amp;&amp; (VV /= ys) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len x1)) &amp;&amp; ((len VV) &gt; (len ys))}</span><span class='hs-definition'>pivApp</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>piv</span></a> <span class='hs-conid'>[]</span>     <a class=annot href="#"><span class=annottext>[{VV : a | (piv &lt;= VV)}]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt;</span><span class='hs-varid'>ys</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == piv)}</span><span class='hs-varid'>piv</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:{VV : a | (VV &gt;= piv)}
-&gt; xs:[{VV : a&lt;p x&gt; | (VV &gt;= piv)}]&lt;p&gt;
-&gt; {VV : [{VV : a | (VV &gt;= piv)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (piv &lt;= VV)}]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | (VV == ys) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
<span class=hs-linenum>517: </span><span class='hs-definition'>pivApp</span> <span class='hs-varid'>piv</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varid'>ys</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x) &amp;&amp; (VV &lt; piv)}</span><span class='hs-varid'>x</span></a>   <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:{VV : a | (VV &gt;= x)}
-&gt; xs:[{VV : a&lt;p x&gt; | (VV &gt;= x)}]&lt;p&gt;
-&gt; {VV : [{VV : a | (VV &gt;= x)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
piv:a
-&gt; x1:[{VV : a | (VV &lt; piv)}]&lt;\x3 VV -&gt; (VV &gt;= x3)&gt;
-&gt; ys:[{VV : a | (piv &lt;= VV)}]&lt;\x2 VV -&gt; (x2 &lt;= VV)&gt;
-&gt; {VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV /= x1) &amp;&amp; (VV /= ys) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len x1)) &amp;&amp; ((len VV) &gt; (len ys))}</span><span class='hs-varid'>pivApp</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == piv)}</span><span class='hs-varid'>piv</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= x) &amp;&amp; (VV &lt; piv)}]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (piv &lt;= VV)}]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | (VV == ys) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
</pre>

Now, LiquidHaskell infers that 


<pre><span class=hs-linenum>523: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>pivApp</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>piv</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> 
<span class=hs-linenum>524: </span>           <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-keyword'>{v:</span><span class='hs-definition'>a</span> <span class='hs-keyword'>| v &lt;  piv}</span> 
<span class=hs-linenum>525: </span>           <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-keyword'>{v:</span><span class='hs-definition'>a</span> <span class='hs-keyword'>| v &gt;= piv}</span> 
<span class=hs-linenum>526: </span>           <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>527: </span>  <span class='hs-keyword'>@-}</span>
</pre>

And we can use `pivApp` to define `quickSort' simply as:


<pre><span class=hs-linenum>533: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>quickSort</span>    <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>534: </span><a class=annot href="#"><span class=annottext>forall a. (GHC.Classes.Ord a) =&gt; [a] -&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-definition'>quickSort</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
{VV : [{VV : a | false}]&lt;p&gt; | (((null VV)) &lt;=&gt; true) &amp;&amp; ((len VV) == 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>535: </span><span class='hs-definition'>quickSort</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>piv:a
-&gt; [{VV : a | (VV &lt; piv)}]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;
-&gt; [{VV : a | (VV &gt;= piv)}]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;
-&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-varid'>pivApp</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &lt; x)}]&lt;\xi VV -&gt; (xi &lt;= VV)&gt; | (VV == lts) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>lts</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= x)}]&lt;\xi VV -&gt; (xi &lt;= VV)&gt; | (VV == gts) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>gts</span></a> 
<span class=hs-linenum>536: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>537: </span>    <a class=annot href="#"><span class=annottext>[{VV : a | (VV &lt; x)}]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-varid'>lts</span></a>          <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[{VV : a | (VV &lt; x)}]
-&gt; [{VV : a | (VV &lt; x)}]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-varid'>quickSort</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &lt; x)}]&lt;\_ VV -&gt; (VV &lt; x)&gt; | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len xs))}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>y</span> <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : (GHC.Types.Bool) | (((Prop VV)) &lt;=&gt; (x &lt; y))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>]</span>
<span class=hs-linenum>538: </span>    <a class=annot href="#"><span class=annottext>[{VV : a | (VV &gt;= x)}]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-varid'>gts</span></a>          <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[{VV : a | (VV &gt;= x)}]
-&gt; [{VV : a | (VV &gt;= x)}]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-varid'>quickSort</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= x)}]&lt;\_ VV -&gt; (VV &gt;= x)&gt; | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len xs))}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>z</span></a> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>z</span> <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>z</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : (GHC.Types.Bool) | (((Prop VV)) &lt;=&gt; (x &gt;= y))}</span><span class='hs-varop'>&gt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span>
</pre>

Really Sorting Lists
--------------------

The convenient thing about our encoding is that the 
underlying datatype is plain Haskell lists. 
This yields two very concrete benefits. 
First, as mentioned before, we can manipulate 
sorted lists with the same functions we'd use 
for regular lists.
Second, by decoupling (or rather, parameterizing)
the relation or property or invariant from the actual 
data structure we can plug in different invariants, 
sometimes in the *same* program.

To see why this is useful, lets look at a *real-world* 
sorting algorithm: the one used inside GHC's 
`Data.List` [module][data-list].


<pre><span class=hs-linenum>560: </span><span class='hs-definition'>sort</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>561: </span><a class=annot href="#"><span class=annottext>forall a. (GHC.Classes.Ord a) =&gt; [a] -&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-definition'>sort</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}
-&gt; {VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}</span><span class='hs-varid'>mergeAll</span></a> <a class=annot href="#"><span class=annottext>forall &lt;q :: [a]-&gt; [[a]]-&gt; Bool, p :: [[a]]-&gt; [a]-&gt; Bool&gt;.
(x:{VV : [{VV : [a]&lt;\x5 VV -&gt; (VV &gt;= x5)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}
 -&gt; {VV : [a]&lt;\x4 VV -&gt; (VV &gt;= x4)&gt;&lt;p x&gt; | ((len VV) &gt;= 0)})
-&gt; (y:[a]
    -&gt; {VV : [{VV : [a]&lt;\x5 VV -&gt; (VV &gt;= x5)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt;&lt;q y&gt; | ((len VV) &gt; 0)})
-&gt; x:[a]
-&gt; exists [z:{VV : [{VV : [a]&lt;\x5 VV -&gt; (VV &gt;= x5)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt;&lt;q x&gt; | ((len VV) &gt; 0)}].{VV : [a]&lt;\x4 VV -&gt; (VV &gt;= x4)&gt;&lt;p z&gt; | ((len VV) &gt;= 0)}</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>[a]
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>sequences</span></a>
<span class=hs-linenum>562: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>563: </span>    <a class=annot href="#"><span class=annottext>[a]
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>sequences</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>a</span><span class='hs-conop'>:</span><span class='hs-varid'>b</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>564: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x:a
-&gt; y:a
-&gt; {VV : (GHC.Types.Ordering) | ((VV == GHC.Types.EQ) &lt;=&gt; (x == y)) &amp;&amp; ((VV == GHC.Types.GT) &lt;=&gt; (x &gt; y)) &amp;&amp; ((VV == GHC.Types.LT) &lt;=&gt; (x &lt; y))}</span><span class='hs-varop'>`compare`</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Ordering)
-&gt; y:(GHC.Types.Ordering)
-&gt; {VV : (GHC.Types.Bool) | (((Prop VV)) &lt;=&gt; (x == y))}</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Ordering) | (VV == GHC.Types.GT) &amp;&amp; ((cmp VV) == GHC.Types.GT)}</span><span class='hs-conid'>GT</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a:a
-&gt; {VV : [{VV : a | (VV &gt; a)}]&lt;\x2 VV -&gt; (VV &gt; a) &amp;&amp; (VV &gt; x2)&gt; | ((len VV) &gt; 0)}
-&gt; {VV : [a] | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>descending</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV == a) &amp;&amp; (VV &gt; b)}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a><span class='hs-keyglyph'>]</span>  <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>565: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>           <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a:a
-&gt; (x1:{VV : [{VV : a | (VV &gt;= a)}]&lt;\x3 VV -&gt; (VV &gt;= a) &amp;&amp; (VV &gt;= x3)&gt; | ((len VV) &gt; 0)}
    -&gt; {VV : [a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt; | (VV /= x1) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len x1))})
-&gt; {VV : [a] | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>ascending</span></a>  <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:{VV : a | (VV &gt;= a)}
-&gt; xs:[{VV : a&lt;p x&gt; | (VV &gt;= a)}]&lt;p&gt;
-&gt; {VV : [{VV : a | (VV &gt;= a)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>566: </span>    <span class='hs-varid'>sequences</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | false}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; true) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV == a)}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>567: </span>    <span class='hs-varid'>sequences</span> <span class='hs-conid'>[]</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | false}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; true) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; true) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-conid'>[]</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>568: </span>
<span class=hs-linenum>569: </span>    <a class=annot href="#"><span class=annottext>a:a
-&gt; {VV : [{VV : a | (VV &gt; a)}]&lt;\x2 VV -&gt; (VV &gt; a) &amp;&amp; (VV &gt; x2)&gt; | ((len VV) &gt; 0)}
-&gt; {VV : [a] | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>descending</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt; a)}]&lt;\x1 VV -&gt; (VV &gt; a) &amp;&amp; (VV &gt; x1)&gt; | ((len VV) &gt; 0)}</span><span class='hs-keyword'>as</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>b</span><span class='hs-conop'>:</span><span class='hs-varid'>bs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>570: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x:a
-&gt; y:a
-&gt; {VV : (GHC.Types.Ordering) | ((VV == GHC.Types.EQ) &lt;=&gt; (x == y)) &amp;&amp; ((VV == GHC.Types.GT) &lt;=&gt; (x &gt; y)) &amp;&amp; ((VV == GHC.Types.LT) &lt;=&gt; (x &lt; y))}</span><span class='hs-varop'>`compare`</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Ordering)
-&gt; y:(GHC.Types.Ordering)
-&gt; {VV : (GHC.Types.Bool) | (((Prop VV)) &lt;=&gt; (x == y))}</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Ordering) | (VV == GHC.Types.GT) &amp;&amp; ((cmp VV) == GHC.Types.GT)}</span><span class='hs-conid'>GT</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a:a
-&gt; {VV : [{VV : a | (VV &gt; a)}]&lt;\x2 VV -&gt; (VV &gt; a) &amp;&amp; (VV &gt; x2)&gt; | ((len VV) &gt; 0)}
-&gt; {VV : [a] | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>descending</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:{VV : a | (VV &gt; b) &amp;&amp; (VV &gt;= a)}
-&gt; xs:[{VV : a&lt;p x&gt; | (VV &gt; b) &amp;&amp; (VV &gt;= a)}]&lt;p&gt;
-&gt; {VV : [{VV : a | (VV &gt; b) &amp;&amp; (VV &gt;= a)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt; a)}]&lt;\x1 VV -&gt; (VV &gt; a) &amp;&amp; (VV &gt; x1)&gt; | (VV == as) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyword'>as</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == bs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>bs</span></a>
<span class=hs-linenum>571: </span>    <span class='hs-varid'>descending</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>as</span> <span class='hs-varid'>bs</span>      <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:{VV : a | (VV &gt;= a)}
-&gt; xs:[{VV : a&lt;p x&gt; | (VV &gt;= a)}]&lt;p&gt;
-&gt; {VV : [{VV : a | (VV &gt;= a)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt; a)}]&lt;\x1 VV -&gt; (VV &gt; a) &amp;&amp; (VV &gt; x1)&gt; | (VV == as) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyword'>as</span></a><span class='hs-layout'>)</span><a class=annot href="#"><span class=annottext>forall &lt;p :: [a]-&gt; [a]-&gt; Bool&gt;.
x:{VV : [a]&lt;\x3 VV -&gt; (VV &gt;= x3)&gt; | ((len VV) &gt;= 0)}
-&gt; xs:[{VV : [a]&lt;\x3 VV -&gt; (VV &gt;= x3)&gt;&lt;p x&gt; | ((len VV) &gt;= 0)}]&lt;p&gt;
-&gt; {VV : [{VV : [a]&lt;\x3 VV -&gt; (VV &gt;= x3)&gt; | ((len VV) &gt;= 0)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>[a]
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>sequences</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | ((len VV) &gt;= 0)}</span><span class='hs-varid'>bs</span></a>
<span class=hs-linenum>572: </span>
<span class=hs-linenum>573: </span>    <a class=annot href="#"><span class=annottext>a:a
-&gt; (x1:{VV : [{VV : a | (VV &gt;= a)}]&lt;\x3 VV -&gt; (VV &gt;= a) &amp;&amp; (VV &gt;= x3)&gt; | ((len VV) &gt; 0)}
    -&gt; {VV : [a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt; | (VV /= x1) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len x1))})
-&gt; {VV : [a] | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>ascending</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x1:{VV : [{VV : a | (VV &gt;= a)}]&lt;\x2 VV -&gt; (VV &gt;= a) &amp;&amp; (VV &gt;= x2)&gt; | ((len VV) &gt; 0)}
-&gt; {VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV /= x1) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len x1))}</span><span class='hs-keyword'>as</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>b</span><span class='hs-conop'>:</span><span class='hs-varid'>bs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>574: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x:a
-&gt; y:a
-&gt; {VV : (GHC.Types.Ordering) | ((VV == GHC.Types.EQ) &lt;=&gt; (x == y)) &amp;&amp; ((VV == GHC.Types.GT) &lt;=&gt; (x &gt; y)) &amp;&amp; ((VV == GHC.Types.LT) &lt;=&gt; (x &lt; y))}</span><span class='hs-varop'>`compare`</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Ordering)
-&gt; y:(GHC.Types.Ordering)
-&gt; {VV : (GHC.Types.Bool) | (((Prop VV)) &lt;=&gt; (x /= y))}</span><span class='hs-varop'>/=</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Ordering) | (VV == GHC.Types.GT) &amp;&amp; ((cmp VV) == GHC.Types.GT)}</span><span class='hs-conid'>GT</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a:a
-&gt; (x1:{VV : [{VV : a | (VV &gt;= a)}]&lt;\x3 VV -&gt; (VV &gt;= a) &amp;&amp; (VV &gt;= x3)&gt; | ((len VV) &gt; 0)}
    -&gt; {VV : [a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt; | (VV /= x1) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len x1))})
-&gt; {VV : [a] | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>ascending</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>ys:{VV : [{VV : a | (VV &gt;= a) &amp;&amp; (VV &gt;= b)}]&lt;\x2 VV -&gt; (VV &gt;= a) &amp;&amp; (VV &gt;= b) &amp;&amp; (VV &gt;= x2)&gt; | ((len VV) &gt; 0)}
-&gt; {VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV /= ys) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len ys))}</span><span class='hs-keyglyph'>\</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= a) &amp;&amp; (VV &gt;= b)}]&lt;\x1 VV -&gt; (VV &gt;= a) &amp;&amp; (VV &gt;= b) &amp;&amp; (VV &gt;= x1)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>ys</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>x1:{VV : [{VV : a | (VV &gt;= a)}]&lt;\x2 VV -&gt; (VV &gt;= a) &amp;&amp; (VV &gt;= x2)&gt; | ((len VV) &gt; 0)}
-&gt; {VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV /= x1) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len x1))}</span><span class='hs-keyword'>as</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x:{VV : a | (VV &gt;= a)}
-&gt; xs:[{VV : a&lt;p x&gt; | (VV &gt;= a)}]&lt;p&gt;
-&gt; {VV : [{VV : a | (VV &gt;= a)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= a) &amp;&amp; (VV &gt;= b)}]&lt;\x1 VV -&gt; (VV &gt;= a) &amp;&amp; (VV &gt;= b) &amp;&amp; (VV &gt;= x1)&gt; | (VV == ys) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == bs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>bs</span></a>
<span class=hs-linenum>575: </span>    <span class='hs-varid'>ascending</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>as</span> <span class='hs-varid'>bs</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{VV : [{VV : a | (VV &gt;= a)}]&lt;\x2 VV -&gt; (VV &gt;= a) &amp;&amp; (VV &gt;= x2)&gt; | ((len VV) &gt; 0)}
-&gt; {VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV /= x1) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len x1))}</span><span class='hs-keyword'>as</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV == a)}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a><span class='hs-keyglyph'>]</span><a class=annot href="#"><span class=annottext>forall &lt;p :: [a]-&gt; [a]-&gt; Bool&gt;.
x:{VV : [a]&lt;\x3 VV -&gt; (VV &gt;= x3)&gt; | ((len VV) &gt;= 0)}
-&gt; xs:[{VV : [a]&lt;\x3 VV -&gt; (VV &gt;= x3)&gt;&lt;p x&gt; | ((len VV) &gt;= 0)}]&lt;p&gt;
-&gt; {VV : [{VV : [a]&lt;\x3 VV -&gt; (VV &gt;= x3)&gt; | ((len VV) &gt;= 0)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>[a]
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>sequences</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | ((len VV) &gt;= 0)}</span><span class='hs-varid'>bs</span></a>
<span class=hs-linenum>576: </span>
<span class=hs-linenum>577: </span>    <a class=annot href="#"><span class=annottext>{VV : [{VV : [a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0)}
-&gt; {VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}</span><span class='hs-varid'>mergeAll</span></a> <span class='hs-keyglyph'>[</span><span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV == x) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>578: </span>    <span class='hs-varid'>mergeAll</span> <span class='hs-varid'>xs</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0)}
-&gt; {VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}</span><span class='hs-varid'>mergeAll</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:{VV : [{VV : [a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))}</span><span class='hs-varid'>mergePairs</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>579: </span>
<span class=hs-linenum>580: </span>    <a class=annot href="#"><span class=annottext>x1:{VV : [{VV : [a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))}</span><span class='hs-varid'>mergePairs</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>a</span><span class='hs-conop'>:</span><span class='hs-varid'>b</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;
-&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt; -&gt; [a]&lt;\xi VV -&gt; (xi &lt;= VV)&gt;</span><span class='hs-varid'>merge</span></a> <a class=annot href="#"><span class=annottext>{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV == a) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV == b) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>b</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: [a]-&gt; [a]-&gt; Bool&gt;.
x:{VV : [a]&lt;\x3 VV -&gt; (x3 &lt;= VV)&gt; | ((len VV) &gt;= 0)}
-&gt; xs:[{VV : [a]&lt;\x3 VV -&gt; (x3 &lt;= VV)&gt;&lt;p x&gt; | ((len VV) &gt;= 0)}]&lt;p&gt;
-&gt; {VV : [{VV : [a]&lt;\x3 VV -&gt; (x3 &lt;= VV)&gt; | ((len VV) &gt;= 0)}]&lt;p&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) == (1 + (len xs)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>x1:{VV : [{VV : [a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))}</span><span class='hs-varid'>mergePairs</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>581: </span>    <span class='hs-varid'>mergePairs</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | false}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; true) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | (VV == a) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>582: </span>    <span class='hs-varid'>mergePairs</span> <span class='hs-conid'>[]</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: [a]-&gt; [a]-&gt; Bool&gt;.
{VV : [{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | false}]&lt;p&gt; | (((null VV)) &lt;=&gt; true) &amp;&amp; ((len VV) == 0)}</span><span class='hs-conid'>[]</span></a>
</pre>

The interesting thing about the procedure is that it 
generates some intermediate lists that are increasing 
*and* others that are decreasing, and then somehow
miraculously whips this whirlygig into a single 
increasing list.

Yet, to check this rather tricky algorithm with 
LiquidHaskell we need merely write:


<pre><span class=hs-linenum>595: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>sort</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncrList</span> <span class='hs-varid'>a</span>  <span class='hs-keyword'>@-}</span>
</pre>



[blog-absref]:     /blog/2013/06/3/abstracting-over-refinements.lhs/
[blog-absref-vec]: http://goto.ucsd.edu/~rjhala/liquid/abstract_refinement_types.pdf
[data-list]:        http://www.haskell.org/ghc/docs/latest/html/libraries/base/src/Data-List.html#sort
[omega-sort]:      http://web.cecs.pdx.edu/~sheard/Code/InsertMergeSort.html
[hasochism]:       https://personal.cis.strath.ac.uk/conor.mcbride/pub/hasochism.pdf

