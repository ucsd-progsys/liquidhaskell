---
layout: post
title: Bounding Vectors
date: 2013-01-30 16:12
author: Ranjit Jhala
published: true 
comments: true
tags:
   - basic
demo: vectorbounds.hs
---

Hopefully, [these][ref101] [articles[ref102] gave you a basic idea about 
what basic refinement types look like. Today, lets move on to some 
fancier properties, namely, the static verification of 
**vector access bounds**. Along the way, we'll see some examples that
illustrate how LiquidHaskell reasons about *recursion*, 
*higher-order functions*, *data types*, and *polymorphism*.

<!-- more -->


<pre><span class=hs-linenum>23: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>VectorBounds</span> <span class='hs-layout'>(</span>
<span class=hs-linenum>24: </span>    <span class='hs-varid'>safeLookup</span> 
<span class=hs-linenum>25: </span>  <span class='hs-layout'>,</span> <span class='hs-varid'>unsafeLookup</span><span class='hs-layout'>,</span> <span class='hs-varid'>unsafeLookup'</span>
<span class=hs-linenum>26: </span>  <span class='hs-layout'>,</span> <span class='hs-varid'>absoluteSum</span><span class='hs-layout'>,</span> <span class='hs-varid'>absoluteSum'</span>
<span class=hs-linenum>27: </span>  <span class='hs-layout'>,</span> <span class='hs-varid'>dotProduct</span>
<span class=hs-linenum>28: </span>  <span class='hs-layout'>,</span> <span class='hs-varid'>sparseProduct</span><span class='hs-layout'>,</span> <span class='hs-varid'>sparseProduct'</span>
<span class=hs-linenum>29: </span>  <span class='hs-layout'>)</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>30: </span>
<span class=hs-linenum>31: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span>      <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>length</span><span class='hs-layout'>)</span>
<span class=hs-linenum>32: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>List</span>    <span class='hs-layout'>(</span><span class='hs-varid'>foldl'</span><span class='hs-layout'>)</span>
<span class=hs-linenum>33: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Vector</span>  <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>foldl'</span><span class='hs-layout'>)</span> 
</pre>

Specifying Bounds for Vectors
-----------------------------

One [classical][dmlarray] use-case for refinement types is to verify
the safety of accesses of arrays and vectors and such, by proving that the 
indices used in such accesses are *within* the vector bounds. 
In this article, we will illustrate this use case by writing a few short
functions that manipulate vectors, in particular, those from the popular
[vector][vec] library. 

To start off, lets **specify** bounds safety by *refining* the types for
the [key functions][vecspec] exported by the module `Data.Vector`. 

Specifications for `Data.Vector`
<pre><span class=hs-linenum>50: </span><span class='hs-keyword'>module</span> <span class='hs-varid'>spec</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Vector</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>51: </span>
<span class=hs-linenum>52: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>GHC</span><span class='hs-varop'>.</span><span class='hs-conid'>Base</span>
<span class=hs-linenum>53: </span>
<span class=hs-linenum>54: </span><span class='hs-definition'>measure</span> <span class='hs-varid'>vlen</span>    <span class='hs-keyglyph'>::</span>   <span class='hs-layout'>(</span><span class='hs-conid'>Vector</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> 
<span class=hs-linenum>55: </span><span class='hs-definition'>assume</span> <span class='hs-varid'>length</span>   <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Vector</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>vlen</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>56: </span><span class='hs-definition'>assume</span> <span class='hs-varop'>!</span>        <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Vector</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-num'>0</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-layout'>(</span><span class='hs-varid'>v</span> <span class='hs-varop'>&lt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>vlen</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> 
</pre>

In particular, we 

- **define** a *property* called `vlen` which denotes the size of the vector,
- **assume** that the `length` function *returns* an integer equal to the vector's size, and
- **assume** that the lookup function `!` *requires* an index between `0` and the vector's size.

There are several things worth paying close attention to in the above snippet.

**Measures**

Measures define auxiliary (or so-called **ghost**) properties of data
values that are useful for specification and verification, but which 
*don't actually exist at run-time*. Thus, they will *only appear in specifications*,
i.e. inside type refinements, but *never* inside code. Often we will use
helper functions like `length` in this case, which *pull* or *materialize*
the ghost values from the refinement world into the actual code world.

**Assumes**

We write `assume` because in this scenario we are not *verifying* the
implementation of `Data.Vector`, we are simply *using* the properties of
the library to verify client code.  If we wanted to verify the library
itself, we would ascribe the above types to the relevant functions in the
Haskell source for `Data.Vector`. 

**Dependent Refinements**

Notice that in the function type (e.g. for `length`) we have *named* the *input*
parameter `x` so that we can refer to it in the *output* refinement. 

 In this case, the type 
<pre><span class=hs-linenum>90: </span><span class='hs-definition'>assume</span> <span class='hs-varid'>length</span>   <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Vector</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>vlen</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>

states that the `Int` output is exactly equal to the size of the input `Vector` named `x`.

In other words, the output refinement **depends on** the input value, which
crucially allows us to write properties that *relate* different program values.

**Verifying a Simple Wrapper**

Lets try write some simple functions to sanity check the above specifications. 
First, consider an *unsafe* vector lookup function:


<pre><span class=hs-linenum>104: </span><a class=annot href="#"><span class=annottext>forall a.
vec:(Vector a) -&gt; {VV : (Int) | (VV &lt; vlen([vec])),(0 &lt;= VV)} -&gt; a</span><span class='hs-definition'>unsafeLookup</span></a> <a class=annot href="#"><span class=annottext>(Vector a)</span><span class='hs-varid'>vec</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0),(VV &lt; vlen([vec])),(0 &lt;= VV)}</span><span class='hs-varid'>index</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Vector a) | (VV = vec),(vlen([VV]) &gt;= 0)}</span><span class='hs-varid'>vec</span></a> <a class=annot href="#"><span class=annottext>x:(Vector a) -&gt; {VV : (Int) | (VV &lt; vlen([x])),(0 &lt;= VV)} -&gt; a</span><span class='hs-varop'>!</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = index),(VV &gt;= 0),(VV &lt; vlen([vec])),(0 &lt;= VV)}</span><span class='hs-varid'>index</span></a>
</pre>

If we run this through LiquidHaskell, it will spit back a type error for
the expression `x ! i` because (happily!) it cannot prove that `index` is
between `0` and the `vlen vec`. Of course, we can specify the bounds 
requirement in the input type


<pre><span class=hs-linenum>113: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>unsafeLookup</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>vec</span><span class='hs-conop'>:</span><span class='hs-conid'>Vector</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>114: </span>                 <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| (0 &lt;= v &amp;&amp; v &lt; (vlen vec))}</span> 
<span class=hs-linenum>115: </span>                 <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>116: </span>  <span class='hs-keyword'>@-}</span>
</pre>

then LiquidHaskell is happy to verify the lookup. Of course, now the burden
of ensuring the index is valid is pushed to clients of `unsafeLookup`.

Instead, we might write a *safe* lookup function that performs the *bounds check*
before looking up the vector:


<pre><span class=hs-linenum>126: </span><a class=annot href="#"><span class=annottext>forall a.
{VV : (Vector {VV : a | false}) | false}
-&gt; {VV : (Int) | false} -&gt; {VV : (Maybe {VV : a | false}) | false}</span><span class='hs-definition'>safeLookup</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vector {VV : a | false}) | false}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | false}</span><span class='hs-varid'>i</span></a> 
<span class=hs-linenum>127: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (Int) | false}
-&gt; y:{VV : (Int) | false}
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | false}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x:(Bool)
-&gt; y:(Bool)
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; &amp;&amp; [(? Prop([x]));
                                          (? Prop([y]))])}</span><span class='hs-varop'>&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | false}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (Int) | false}
-&gt; y:{VV : (Int) | false}
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt; y))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>x:(Vector {VV : a | false})
-&gt; {VV : (Int) | (VV = vlen([x])),(VV &gt;= 0)}</span><span class='hs-varid'>length</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vector {VV : a | false}) | false}</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:{VV : a | false}
-&gt; {VV : (Maybe {VV : a | false}) | ((? isJust([VV])) &lt;=&gt; true),
                                    (fromJust([VV]) = x)}</span><span class='hs-conid'>Just</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Vector {VV : a | false}) | false}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:(Vector {VV : a | false})
-&gt; {VV : (Int) | (VV &lt; vlen([x])),(0 &lt;= VV)} -&gt; {VV : a | false}</span><span class='hs-varop'>!</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | false}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>128: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>              <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Maybe {VV : a | false}) | ((? isJust([VV])) &lt;=&gt; false)}</span><span class='hs-conid'>Nothing</span></a> 
</pre>

**Predicate Aliases**

The type for `unsafeLookup` above is rather verbose as we have to spell out
the upper and lower bounds and conjoin them. Just as we enjoy abstractions
when programming, we will find it handy to have abstractions in the
specification mechanism. To this end, LiquidHaskell supports 
*predicate aliases*, which are best illustrated by example


<pre><span class=hs-linenum>140: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>Btwn</span> <span class='hs-conid'>Lo</span> <span class='hs-conid'>I</span> <span class='hs-conid'>Hi</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Lo</span> <span class='hs-varop'>&lt;=</span> <span class='hs-conid'>I</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-conid'>I</span> <span class='hs-varop'>&lt;</span> <span class='hs-conid'>Hi</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>141: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>InBounds</span> <span class='hs-conid'>I</span> <span class='hs-conid'>A</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Btwn</span> <span class='hs-num'>0</span> <span class='hs-conid'>I</span> <span class='hs-layout'>(</span><span class='hs-varid'>vlen</span> <span class='hs-conid'>A</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>

Now, we can simplify the type for the unsafe lookup function to


<pre><span class=hs-linenum>147: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>unsafeLookup'</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Vector</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| (InBounds v x)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>148: </span><span class='hs-definition'>unsafeLookup'</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Vector</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>149: </span><a class=annot href="#"><span class=annottext>forall a.
x:(Vector a) -&gt; {VV : (Int) | (VV &lt; vlen([x])),(0 &lt;= VV)} -&gt; a</span><span class='hs-definition'>unsafeLookup'</span></a> <a class=annot href="#"><span class=annottext>(Vector a)</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0),(VV &lt; vlen([x])),(0 &lt;= VV)}</span><span class='hs-varid'>i</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Vector a) | (VV = x),(vlen([VV]) &gt;= 0)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:(Vector a) -&gt; {VV : (Int) | (VV &lt; vlen([x])),(0 &lt;= VV)} -&gt; a</span><span class='hs-varop'>!</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i),(VV &gt;= 0),(VV &lt; vlen([x])),(0 &lt;= VV)}</span><span class='hs-varid'>i</span></a>
</pre>


Our First Recursive Function
----------------------------

OK, with the tedious preliminaries out of the way, lets write some code!

To start: a vanilla recursive function that adds up the absolute values of
the elements of an integer vector.


<pre><span class=hs-linenum>162: </span><span class='hs-definition'>absoluteSum</span>       <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Vector</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> 
<span class=hs-linenum>163: </span><a class=annot href="#"><span class=annottext>(Vector (Int)) -&gt; {VV : (Int) | (0 &lt;= VV)}</span><span class='hs-definition'>absoluteSum</span></a> <a class=annot href="#"><span class=annottext>(Vector (Int))</span><span class='hs-varid'>vec</span></a>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(Int#) -&gt; {VV : (Int) | (VV = (x  :  int))}</span><span class='hs-keyword'>if</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (Int) | (VV &gt;= 0),(0 &lt;= VV),(VV &lt;= n),(VV &lt;= vlen([vec]))}
-&gt; y:{VV : (Int) | (VV &gt;= 0),
                   (0 &lt;= VV),
                   (VV &lt;= n),
                   (VV &lt;= vlen([vec]))}
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt; y))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = n),(VV = vlen([vec])),(VV &gt;= 0)}</span><span class='hs-varid'>n</span></a> <span class='hs-keyword'>then</span> <a class=annot href="#"><span class=annottext>x6:{VV : (Int) | (VV = 0),(VV &lt; n),(VV &lt; vlen([vec])),(0 &lt;= VV)}
-&gt; x4:{VV : (Int) | (VV = 0),
                    (VV = x6),
                    (VV &lt; n),
                    (VV &lt; vlen([vec])),
                    (0 &lt;= VV),
                    (x6 &lt;= VV)}
-&gt; {VV : (Int) | (VV &gt;= 0),
                 (VV &gt;= x6),
                 (VV &gt;= x4),
                 (0 &lt;= VV),
                 (x6 &lt;= VV),
                 (x4 &lt;= VV)}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <span class='hs-keyword'>else</span> <a class=annot href="#"><span class=annottext>x:(Int#) -&gt; {VV : (Int) | (VV = (x  :  int))}</span><span class='hs-num'>0</span></a>
<span class=hs-linenum>164: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>165: </span>    <a class=annot href="#"><span class=annottext>x6:{VV : (Int) | (VV = 0),(VV &lt; n),(VV &lt; vlen([vec])),(0 &lt;= VV)}
-&gt; x4:{VV : (Int) | (VV = 0),
                    (VV = x6),
                    (VV &lt; n),
                    (VV &lt; vlen([vec])),
                    (0 &lt;= VV),
                    (x6 &lt;= VV)}
-&gt; {VV : (Int) | (VV &gt;= 0),
                 (VV &gt;= x6),
                 (VV &gt;= x4),
                 (0 &lt;= VV),
                 (x6 &lt;= VV),
                 (x4 &lt;= VV)}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0),(0 &lt;= VV)}</span><span class='hs-varid'>acc</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0),
              (0 &lt;= VV),
              (VV &lt;= n),
              (VV &lt;= vlen([vec])),
              (VV &lt;= vlen([vec]))}</span><span class='hs-varid'>i</span></a> 
<span class=hs-linenum>166: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i),
              (VV &gt;= 0),
              (0 &lt;= VV),
              (VV &lt;= n),
              (VV &lt;= vlen([vec])),
              (VV &lt;= vlen([vec]))}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (Int) | (VV &gt;= 0),
                (VV &gt;= i),
                (0 &lt;= VV),
                (VV &lt;= n),
                (VV &lt;= vlen([vec])),
                (VV &lt;= vlen([vec])),
                (i &lt;= VV)}
-&gt; y:{VV : (Int) | (VV &gt;= 0),
                   (VV &gt;= i),
                   (0 &lt;= VV),
                   (VV &lt;= n),
                   (VV &lt;= vlen([vec])),
                   (VV &lt;= vlen([vec])),
                   (i &lt;= VV)}
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x != y))}</span><span class='hs-varop'>/=</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = n),(VV = vlen([vec])),(VV &gt;= 0)}</span><span class='hs-varid'>n</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x6:{VV : (Int) | (VV = 0),(VV &lt; n),(VV &lt; vlen([vec])),(0 &lt;= VV)}
-&gt; x4:{VV : (Int) | (VV = 0),
                    (VV = x6),
                    (VV &lt; n),
                    (VV &lt; vlen([vec])),
                    (0 &lt;= VV),
                    (x6 &lt;= VV)}
-&gt; {VV : (Int) | (VV &gt;= 0),
                 (VV &gt;= x6),
                 (VV &gt;= x4),
                 (0 &lt;= VV),
                 (x6 &lt;= VV),
                 (x4 &lt;= VV)}</span><span class='hs-varid'>go</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = acc),(VV &gt;= 0),(0 &lt;= VV)}</span><span class='hs-varid'>acc</span></a> <a class=annot href="#"><span class=annottext>x:(Int) -&gt; y:(Int) -&gt; {VV : (Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>n:(Int) -&gt; {VV : (Int) | (VV &gt;= 0),(VV &gt;= n)}</span><span class='hs-varid'>abz</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Vector (Int)) | (VV = vec),
                       (VV = vec),
                       (vlen([VV]) = vlen([vec])),
                       (vlen([VV]) &gt;= 0)}</span><span class='hs-varid'>vec</span></a> <a class=annot href="#"><span class=annottext>x:(Vector (Int))
-&gt; {VV : (Int) | (VV &lt; vlen([x])),(0 &lt;= VV)} -&gt; (Int)</span><span class='hs-varop'>!</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i),
              (VV &gt;= 0),
              (0 &lt;= VV),
              (VV &lt;= n),
              (VV &lt;= vlen([vec])),
              (VV &lt;= vlen([vec]))}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i),
              (VV &gt;= 0),
              (0 &lt;= VV),
              (VV &lt;= n),
              (VV &lt;= vlen([vec])),
              (VV &lt;= vlen([vec]))}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x:(Int) -&gt; y:(Int) -&gt; {VV : (Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>167: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = acc),(VV &gt;= 0),(0 &lt;= VV)}</span><span class='hs-varid'>acc</span></a> 
<span class=hs-linenum>168: </span>    <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = vlen([vec])),(VV &gt;= 0)}</span><span class='hs-varid'>n</span></a>             <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(Vector (Int)) -&gt; {VV : (Int) | (VV = vlen([x])),(VV &gt;= 0)}</span><span class='hs-varid'>length</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vector (Int)) | (VV = vec),
                       (VV = vec),
                       (vlen([VV]) = vlen([vec])),
                       (vlen([VV]) &gt;= 0)}</span><span class='hs-varid'>vec</span></a>
</pre>

where the function `abz` is the absolute value function from [before][ref101].


<pre><span class=hs-linenum>174: </span><a class=annot href="#"><span class=annottext>forall a.
(Num a) -&gt; (Ord a) -&gt; n:a -&gt; {VV : a | (VV &gt;= 0),(VV &gt;= n)}</span><span class='hs-definition'>abz</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>n</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Integer) | (VV = 0)}</span><span class='hs-keyword'>if</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = n)}</span><span class='hs-varid'>n</span></a> <span class='hs-keyword'>then</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = n)}</span><span class='hs-varid'>n</span></a> <span class='hs-keyword'>else</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>a</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : a | (VV = (x - y))}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = n)}</span><span class='hs-varid'>n</span></a><span class='hs-layout'>)</span> 
</pre>

Digression: Introducing Errors  
------------------------------

If you are following along in the demo page -- I heartily 
recommend that you try the following modifications, 
one at a time, and see what happens.

**What happens if:** 

- You *remove* the check `0 < n` 

- You *replace* the guard with `i <= n`

In each case, LiquidHaskell will grumble that your program is *unsafe*. 
Do you understand why?

Refinement Type Inference
-------------------------

LiquidHaskell happily verifies `absoluteSum` -- or, to be precise, 
the safety of the vector accesses `vec ! i`. The verification works 
out because LiquidHaskell is able **automatically** infer a suitable 
type for `go`. Shuffle your mouse over the identifier above to see 
the inferred type. Observe that the type states that
The first parameter `acc` (and the output) is `0 <= V`. 
That is, the returned value is non-negative.

More importantly, the type states that the second parameter `i` is 
`0 <= V` and `V <= n` and `V <= (vlen vec)`. That is, the parameter `i` 
is between `0` and the vector length (inclusive). LiquidHaskell uses these 
and the test that `i /= n` to establish that `i` is in fact between `0` 
and `(vlen vec)` thereby verifing safety. 

In fact, if we want to use the function externally (i.e. in another module) 
we can go ahead and strengthen its type to specify that the output is 
non-negative.


<pre><span class=hs-linenum>215: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>absoluteSum</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Vector</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| 0 &lt;= v}</span>  <span class='hs-keyword'>@-}</span> 
</pre>

**What happens if:** You *replace* the output type for `absoluteSum` with `{v: Int | 0 < v }` ?

Bottling Recursion With a Higher-Order `loop`
---------------------------------------------

Next, lets refactor the above low-level recursive function 
into a generic higher-order `loop`.


<pre><span class=hs-linenum>227: </span><span class='hs-definition'>loop</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>228: </span><a class=annot href="#"><span class=annottext>forall a.
lo:{VV : (Int) | (0 &lt;= VV)}
-&gt; hi:{VV : (Int) | (0 &lt;= VV),(lo &lt;= VV)}
-&gt; a
-&gt; ({VV : (Int) | (VV &lt; hi),(lo &lt;= VV)} -&gt; a -&gt; a)
-&gt; a</span><span class='hs-definition'>loop</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0),(0 &lt;= VV)}</span><span class='hs-varid'>lo</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0),(VV &gt;= lo),(0 &lt;= VV),(lo &lt;= VV)}</span><span class='hs-varid'>hi</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>base</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0),(VV &gt;= lo),(VV &lt; hi),(0 &lt;= VV),(lo &lt;= VV)}
-&gt; a -&gt; a</span><span class='hs-varid'>f</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = base)}
-&gt; {VV : (Int) | (VV = lo),
                 (VV &gt;= 0),
                 (0 &lt;= VV),
                 (VV &lt;= hi),
                 (lo &lt;= VV)}
-&gt; a</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = base)}</span><span class='hs-varid'>base</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = lo),(VV &gt;= 0),(0 &lt;= VV)}</span><span class='hs-varid'>lo</span></a>
<span class=hs-linenum>229: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>230: </span>    <a class=annot href="#"><span class=annottext>{VV : a | (VV = base)}
-&gt; {VV : (Int) | (VV = lo),
                 (VV &gt;= 0),
                 (0 &lt;= VV),
                 (VV &lt;= hi),
                 (lo &lt;= VV)}
-&gt; a</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>acc</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0),
              (VV &gt;= lo),
              (VV &gt;= lo),
              (0 &lt;= VV),
              (VV &lt;= hi),
              (VV &lt;= hi),
              (lo &lt;= VV),
              (lo &lt;= VV)}</span><span class='hs-varid'>i</span></a>     
<span class=hs-linenum>231: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i),
              (VV &gt;= 0),
              (VV &gt;= lo),
              (VV &gt;= lo),
              (0 &lt;= VV),
              (VV &lt;= hi),
              (VV &lt;= hi),
              (lo &lt;= VV),
              (lo &lt;= VV)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (Int) | (VV &gt;= 0),
                (VV &gt;= i),
                (VV &gt;= lo),
                (VV &gt;= lo),
                (0 &lt;= VV),
                (VV &lt;= hi),
                (VV &lt;= hi),
                (i &lt;= VV),
                (lo &lt;= VV),
                (lo &lt;= VV)}
-&gt; y:{VV : (Int) | (VV &gt;= 0),
                   (VV &gt;= i),
                   (VV &gt;= lo),
                   (VV &gt;= lo),
                   (0 &lt;= VV),
                   (VV &lt;= hi),
                   (VV &lt;= hi),
                   (i &lt;= VV),
                   (lo &lt;= VV),
                   (lo &lt;= VV)}
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x != y))}</span><span class='hs-varop'>/=</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = hi),
              (VV = hi),
              (VV &gt;= 0),
              (VV &gt;= lo),
              (VV &gt;= lo),
              (0 &lt;= VV),
              (hi &lt;= VV),
              (lo &lt;= VV),
              (lo &lt;= VV)}</span><span class='hs-varid'>hi</span></a>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = base)}
-&gt; {VV : (Int) | (VV = lo),
                 (VV &gt;= 0),
                 (0 &lt;= VV),
                 (VV &lt;= hi),
                 (lo &lt;= VV)}
-&gt; a</span><span class='hs-varid'>go</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0),
              (VV &gt;= lo),
              (VV &gt;= lo),
              (VV &lt; hi),
              (VV &lt; hi),
              (0 &lt;= VV),
              (lo &lt;= VV),
              (lo &lt;= VV)}
-&gt; a -&gt; a</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i),
              (VV &gt;= 0),
              (VV &gt;= lo),
              (VV &gt;= lo),
              (0 &lt;= VV),
              (VV &lt;= hi),
              (VV &lt;= hi),
              (lo &lt;= VV),
              (lo &lt;= VV)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = acc)}</span><span class='hs-varid'>acc</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i),
              (VV &gt;= 0),
              (VV &gt;= lo),
              (VV &gt;= lo),
              (0 &lt;= VV),
              (VV &lt;= hi),
              (VV &lt;= hi),
              (lo &lt;= VV),
              (lo &lt;= VV)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x:(Int) -&gt; y:(Int) -&gt; {VV : (Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>232: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = acc)}</span><span class='hs-varid'>acc</span></a>
</pre>

**Using `loop` to compute `absoluteSum`**

We can now use `loop` to implement `absoluteSum` like so:


<pre><span class=hs-linenum>240: </span><a class=annot href="#"><span class=annottext>forall a.
(Num a)
-&gt; {VV : (Vector {VV : a | false}) | false} -&gt; {VV : a | false}</span><span class='hs-definition'>absoluteSum'</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vector {VV : a | false}) | false}</span><span class='hs-varid'>vec</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Integer) | (VV = 0)}</span><span class='hs-keyword'>if</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (Int) | false}
-&gt; y:{VV : (Int) | false}
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt; y))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = n),(VV = vlen([vec])),(VV &gt;= 0)}</span><span class='hs-varid'>n</span></a> <span class='hs-keyword'>then</span> <a class=annot href="#"><span class=annottext>lo:{VV : (Int) | (0 &lt;= VV)}
-&gt; hi:{VV : (Int) | (0 &lt;= VV),(lo &lt;= VV)}
-&gt; {VV : a | false}
-&gt; ({VV : (Int) | (VV &lt; hi),(lo &lt;= VV)}
    -&gt; {VV : a | false} -&gt; {VV : a | false})
-&gt; {VV : a | false}</span><span class='hs-varid'>loop</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = n),(VV = vlen([vec])),(VV &gt;= 0)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | false} -&gt; {VV : a | false} -&gt; {VV : a | false}</span><span class='hs-varid'>body</span></a> <span class='hs-keyword'>else</span> <a class=annot href="#"><span class=annottext>{VV : (Integer) | (VV = 0)}</span><span class='hs-num'>0</span></a>
<span class=hs-linenum>241: </span>  <span class='hs-keyword'>where</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | false} -&gt; {VV : a | false} -&gt; {VV : a | false}</span><span class='hs-varid'>body</span></a>     <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>\</span><a class=annot href="#"><span class=annottext>{VV : (Int) | false}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>{VV : a | false}</span><span class='hs-varid'>acc</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{VV : a | false}</span><span class='hs-varid'>acc</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : a | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Vector {VV : a | false}) | false}</span><span class='hs-varid'>vec</span></a> <a class=annot href="#"><span class=annottext>x:(Vector {VV : a | false})
-&gt; {VV : (Int) | (VV &lt; vlen([x])),(0 &lt;= VV)} -&gt; {VV : a | false}</span><span class='hs-varop'>!</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | false}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>242: </span>        <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = vlen([vec])),(VV &gt;= 0)}</span><span class='hs-varid'>n</span></a>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(Vector {VV : a | false})
-&gt; {VV : (Int) | (VV = vlen([x])),(VV &gt;= 0)}</span><span class='hs-varid'>length</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vector {VV : a | false}) | false}</span><span class='hs-varid'>vec</span></a>
</pre>

LiquidHaskell verifies `absoluteSum'` without any trouble.

It is very instructive to see the type that LiquidHaskell *infers* 
for `loop` -- it looks something like


<pre><span class=hs-linenum>251: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>loop</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>lo</span><span class='hs-conop'>:</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| (0 &lt;= v) }</span>  
<span class=hs-linenum>252: </span>         <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>hi</span><span class='hs-conop'>:</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| ((0 &lt;= v) &amp;&amp; (lo &lt;= v))}</span> 
<span class=hs-linenum>253: </span>         <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>254: </span>         <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-conop'>:</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| (Btwn lo v hi)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>255: </span>         <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>256: </span>  <span class='hs-keyword'>@-}</span>
</pre>

In english, the above type states that 

- `lo` the loop *lower* bound is a non-negative integer
- `hi` the loop *upper* bound is a greater than `lo`,
- `f`  the loop *body* is only called with integers between `lo` and `hi`.

Inference is a rather convenient option -- it can be tedious to have to keep 
typing things like the above! Of course, if we wanted to make `loop` a
public or exported function, we could use the inferred type to generate 
an explicit signature too.

At the call 
<pre><span class=hs-linenum>271: </span><span class='hs-definition'>loop</span> <span class='hs-num'>0</span> <span class='hs-varid'>n</span> <span class='hs-num'>0</span> <span class='hs-varid'>body</span> 
</pre>

the parameters `lo` and `hi` are instantiated with `0` and `n` respectively
(which, by the way is where the inference engine deduces non-negativity
from) and thus LiquidHaskell concludes that `body` is only called with
values of `i` that are *between* `0` and `(vlen vec)`, which shows the 
safety of the call `vec ! i`.

**Using `loop` to compute `dotProduct`**

Here's another use of `loop` -- this time to compute the `dotProduct` 
of two vectors. 


<pre><span class=hs-linenum>286: </span><span class='hs-definition'>dotProduct</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Vector</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Vector</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>287: </span><a class=annot href="#"><span class=annottext>x:(Vector (Int))
-&gt; {VV : (Vector (Int)) | (vlen([VV]) = vlen([x]))} -&gt; (Int)</span><span class='hs-definition'>dotProduct</span></a> <a class=annot href="#"><span class=annottext>(Vector (Int))</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vector (Int)) | (vlen([VV]) = vlen([x])),(vlen([VV]) &gt;= 0)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>lo:{VV : (Int) | (0 &lt;= VV)}
-&gt; hi:{VV : (Int) | (0 &lt;= VV),(lo &lt;= VV)}
-&gt; (Int)
-&gt; ({VV : (Int) | (VV &lt; hi),(lo &lt;= VV)} -&gt; (Int) -&gt; (Int))
-&gt; (Int)</span><span class='hs-varid'>loop</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x:(Vector (Int)) -&gt; {VV : (Int) | (VV = vlen([x])),(VV &gt;= 0)}</span><span class='hs-varid'>length</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vector (Int)) | (VV = x),(vlen([VV]) &gt;= 0)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0),
              (VV &lt; vlen([x])),
              (VV &lt; vlen([y])),
              (0 &lt;= VV)}
-&gt; (Int) -&gt; (Int)</span><span class='hs-keyglyph'>\</span></a><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0),
              (VV &lt; vlen([x])),
              (VV &lt; vlen([y])),
              (0 &lt;= VV)}</span><span class='hs-varid'>i</span></a> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x:(Int) -&gt; y:(Int) -&gt; {VV : (Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Vector (Int)) | (VV = x),(vlen([VV]) &gt;= 0)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:(Vector (Int))
-&gt; {VV : (Int) | (VV &lt; vlen([x])),(0 &lt;= VV)} -&gt; (Int)</span><span class='hs-varop'>!</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i),
              (VV &gt;= 0),
              (VV &lt; vlen([x])),
              (VV &lt; vlen([y])),
              (0 &lt;= VV)}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x:(Int)
-&gt; y:(Int) -&gt; {VV : (Int) | (&amp;&amp; [(x &gt;= 0); (y &gt;= 0)] =&gt; (VV &gt;= 0))}</span><span class='hs-varop'>*</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Vector (Int)) | (VV = y),
                       (vlen([VV]) = vlen([x])),
                       (vlen([VV]) &gt;= 0)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>x:(Vector (Int))
-&gt; {VV : (Int) | (VV &lt; vlen([x])),(0 &lt;= VV)} -&gt; (Int)</span><span class='hs-varop'>!</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i),
              (VV &gt;= 0),
              (VV &lt; vlen([x])),
              (VV &lt; vlen([y])),
              (0 &lt;= VV)}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> 
</pre>

The gimlet-eyed reader will realize that the above is quite unsafe -- what
if `x` is a 10-dimensional vector while `y` has only 3-dimensions? 

A nasty
<pre><span class=hs-linenum>294: </span><span class='hs-varop'>***</span> <span class='hs-conid'>Exception</span><span class='hs-conop'>:</span> <span class='hs-varop'>./</span><span class='hs-conid'>Data</span><span class='hs-varop'>/</span><span class='hs-conid'>Vector</span><span class='hs-varop'>/</span><span class='hs-conid'>Generic</span><span class='hs-varop'>.</span><span class='hs-varid'>hs</span><span class='hs-conop'>:</span><span class='hs-num'>244</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varop'>!</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-conop'>:</span> <span class='hs-varid'>index</span> <span class='hs-varid'>out</span> <span class='hs-keyword'>of</span> <span class='hs-varid'>bounds</span> <span class='hs-varop'>...</span>
</pre>

*Yech*. 

This is precisely the sort of unwelcome surprise we want to do away with at 
compile-time. Refinements to the rescue! We can specify that the vectors 
have the same dimensions quite easily


<pre><span class=hs-linenum>304: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>dotProduct</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Vector</span> <span class='hs-conid'>Int</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>305: </span>               <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-keyword'>{v:</span> <span class='hs-layout'>(</span><span class='hs-conid'>Vector</span> <span class='hs-conid'>Int</span><span class='hs-layout'>)</span> <span class='hs-keyword'>| (vlen v) = (vlen x)}</span> 
<span class=hs-linenum>306: </span>               <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> 
<span class=hs-linenum>307: </span>  <span class='hs-keyword'>@-}</span>
</pre>

after which LiquidHaskell will gladly verify that the implementation of
`dotProduct` is indeed safe!

Refining Data Types
-------------------

Next, suppose we want to write a *sparse dot product*, that is, 
the dot product of a vector and a **sparse vector** represented
by a list of index-value tuples.

**Representing Sparse Vectors**

We can represent the sparse vector with a **refinement type alias** 


<pre><span class=hs-linenum>325: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>SparseVector</span> <span class='hs-varid'>a</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conid'>Btwn</span> <span class='hs-num'>0</span> <span class='hs-varid'>v</span> <span class='hs-conid'>N</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span><span class='hs-layout'>,</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
</pre>

As with usual types, the alias `SparseVector` on the left is just a 
shorthand for the (longer) type on the right, it does not actually 
define a new type. Thus, the above alias is simply a refinement of
Haskell's `[(Int, a)]` type, with a size parameter `N` that facilitates 
easy specification reuse. In this way, refinements let us express 
invariants of containers like lists in a straightforward manner. 

**Aside:** If you are familiar with the *index-style* length 
encoding e.g. as found in [DML][dml] or [Agda][agdavec], then note
that despite appearances, our `SparseVector` definition is *not* 
indexed. Instead, we deliberately choose to encode properties 
with logical refinement predicates, to facilitate SMT based 
checking and inference.

**Verifying Uses of Sparse Vectors**

Next, we can write a recursive procedure that computes the sparse product


<pre><span class=hs-linenum>347: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>sparseProduct</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Num</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Vector</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>348: </span>                             <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>SparseVector</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-varid'>vlen</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>349: </span>                             <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>350: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>351: </span><a class=annot href="#"><span class=annottext>forall a.
(Num a)
-&gt; x:(Vector a)
-&gt; [({VV : (Int) | (VV &lt; vlen([x])),(0 &lt;= VV)} , a)]
-&gt; a</span><span class='hs-definition'>sparseProduct</span></a> <a class=annot href="#"><span class=annottext>(Vector a)</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>[({VV : (Int) | (VV &gt;= 0),(VV &lt; vlen([x])),(0 &lt;= VV)} , a)]</span><span class='hs-varid'>y</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = 0)}
-&gt; {VV : [({VV : (Int) | (VV &gt;= 0),
                         (VV &lt; vlen([x])),
                         (0 &lt;= VV)} , a)] | (VV = y),
                                            (len([VV]) = len([y])),
                                            (len([VV]) &gt;= 0)}
-&gt; a</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>{VV : [({VV : (Int) | (VV &gt;= 0),
                      (VV &lt; vlen([x])),
                      (0 &lt;= VV)} , a)] | (VV = y),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>y</span></a>
<span class=hs-linenum>352: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>353: </span>    <a class=annot href="#"><span class=annottext>{VV : a | (VV = 0)}
-&gt; {VV : [({VV : (Int) | (VV &gt;= 0),
                         (VV &lt; vlen([x])),
                         (0 &lt;= VV)} , a)] | (VV = y),
                                            (len([VV]) = len([y])),
                                            (len([VV]) &gt;= 0)}
-&gt; a</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>sum</span></a> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-layout'>,</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>y'</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = 0)}
-&gt; {VV : [({VV : (Int) | (VV &gt;= 0),
                         (VV &lt; vlen([x])),
                         (0 &lt;= VV)} , a)] | (VV = y),
                                            (len([VV]) = len([y])),
                                            (len([VV]) &gt;= 0)}
-&gt; a</span><span class='hs-varid'>go</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = sum)}</span><span class='hs-varid'>sum</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : a | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (Vector a) | (VV = x),
                   (VV = x),
                   (vlen([VV]) = vlen([x])),
                   (vlen([VV]) &gt;= 0)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:(Vector a) -&gt; {VV : (Int) | (VV &lt; vlen([x])),(0 &lt;= VV)} -&gt; a</span><span class='hs-varop'>!</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i),
              (VV &gt;= 0),
              (VV &lt; vlen([x])),
              (VV &lt; vlen([x])),
              (0 &lt;= VV)}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : a | (&amp;&amp; [(x &gt;= 0); (y &gt;= 0)] =&gt; (VV &gt;= 0))}</span><span class='hs-varop'>*</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = v)}</span><span class='hs-varid'>v</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [({VV : (Int) | (VV &gt;= 0),
                      (VV &lt; vlen([x])),
                      (VV &lt; vlen([x])),
                      (0 &lt;= VV)} , a)] | (VV = y'),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>y'</span></a> 
<span class=hs-linenum>354: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>sum</span> <span class='hs-conid'>[]</span>            <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = sum)}</span><span class='hs-varid'>sum</span></a>
</pre>

LiquidHaskell verifies the above by using the specification for `y` to
conclude that for each tuple `(i, v)` in the list, the value of `i` is 
within the bounds of the vector `x`, thereby proving the safety of the 
access `x ! i`.

Refinements and Polymorphism
----------------------------

The sharp reader will have undoubtedly noticed that the sparse product 
can be more cleanly expressed as a [fold][foldl]. 

 Indeed! Let us recall the type of the `foldl` operation
<pre><span class=hs-linenum>369: </span><span class='hs-definition'>foldl'</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>b</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
</pre>

Thus, we can simply fold over the sparse vector, accumulating the `sum`
as we go along


<pre><span class=hs-linenum>376: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>sparseProduct'</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Num</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>Vector</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>377: </span>                             <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>SparseVector</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-varid'>vlen</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>378: </span>                             <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>379: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>380: </span><a class=annot href="#"><span class=annottext>forall a.
(Num a)
-&gt; x:(Vector a)
-&gt; [({VV : (Int) | (VV &lt; vlen([x])),(0 &lt;= VV)} , a)]
-&gt; a</span><span class='hs-definition'>sparseProduct'</span></a> <a class=annot href="#"><span class=annottext>(Vector a)</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>[({VV : (Int) | (VV &gt;= 0),(VV &lt; vlen([x])),(0 &lt;= VV)} , a)]</span><span class='hs-varid'>y</span></a>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(a
 -&gt; ({VV : (Int) | (VV &gt;= 0),(VV &lt; vlen([x])),(0 &lt;= VV)} , a) -&gt; a)
-&gt; a
-&gt; [({VV : (Int) | (VV &gt;= 0),(VV &lt; vlen([x])),(0 &lt;= VV)} , a)]
-&gt; a</span><span class='hs-varid'>foldl'</span></a> <a class=annot href="#"><span class=annottext>a -&gt; ({VV : (Int) | (VV &gt;= 0),(VV &lt; vlen([x])),(0 &lt;= VV)} , a) -&gt; a</span><span class='hs-varid'>body</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>{VV : [({VV : (Int) | (VV &gt;= 0),
                      (VV &lt; vlen([x])),
                      (0 &lt;= VV)} , a)] | (VV = y),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>y</span></a>   
<span class=hs-linenum>381: </span>  <span class='hs-keyword'>where</span> <a class=annot href="#"><span class=annottext>a -&gt; ({VV : (Int) | (VV &gt;= 0),(VV &lt; vlen([x])),(0 &lt;= VV)} , a) -&gt; a</span><span class='hs-varid'>body</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>sum</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-layout'>,</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = sum)}</span><span class='hs-varid'>sum</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : a | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (Vector a) | (VV = x),(vlen([VV]) &gt;= 0)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:(Vector a) -&gt; {VV : (Int) | (VV &lt; vlen([x])),(0 &lt;= VV)} -&gt; a</span><span class='hs-varop'>!</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i),(VV &gt;= 0),(VV &lt; vlen([x])),(0 &lt;= VV)}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : a | (&amp;&amp; [(x &gt;= 0); (y &gt;= 0)] =&gt; (VV &gt;= 0))}</span><span class='hs-varop'>*</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = v)}</span><span class='hs-varid'>v</span></a>
</pre>

LiquidHaskell digests this too, without much difficulty. 

The main trick is in how the polymorphism of `foldl'` is instantiated. 

1. The GHC type inference engine deduces that at this site, the type variable
   `b` from the signature of `foldl'` is instantiated to the Haskell type `(Int, a)`. 

2. Correspondingly, LiquidHaskell infers that in fact `b` can be instantiated
   to the *refined* type `({v: Int | (Btwn 0 v (vlen x))}, a)`. 
   
Walk the mouse over to `i` to see this inferred type. (You can also hover over
`foldl'`above to see the rather more verbose fully instantiated type.)

Thus, the inference mechanism saves us a fair bit of typing and allows us to
reuse existing polymorphic functions over containers and such without ceremony.

Conclusion
----------

Thats all for now folks! Hopefully the above gives you a reasonable idea of
how one can use refinements to verify size related properties, and more
generally, to specify and verify properties of recursive, and polymorphic
functions operating over datatypes. Next time, we'll look at how we can
teach LiquidHaskell to think about properties of recursive structures
like lists and trees.

[vecspec]: https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/Vector.spec
[vec]:     http://hackage.haskell.org/package/vector
[dml]:     http://www.cs.bu.edu/~hwxi/DML/DML.html
[agdavec]: http://code.haskell.org/Agda/examples/Vec.agda
[ref101]:  /blog/2013/01/01/refinement-types-101.lhs/ 
[ref102]:  /blog/2013/01/27/refinements-101-reax.lhs/ 
[foldl]:   http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html

[dmlarray]:http://www.cs.bu.edu/~hwxi/academic/papers/pldi98.pdf

