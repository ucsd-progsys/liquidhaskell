---
layout: post
title: Safely Catching A List By Its Tail
date: 2013-01-31 16:12
author: Ranjit Jhala
published: true 
comments: true
tags:
   - measures 
demo: lenMapReduce.hs
---

[Previously][ref101] we [saw][ref102] some examples of how refinements
could be used to encode invariants about basic `Int` values.  Today, let's
see how refinements allow us specify and verify *structural invariants*
about recursive data types like lists. In particular, we will
learn about at a new mechanism called a `measure`, 
use measures to describe the **length** of a list, and 
use the resulting refinement types to obtain compile-time assurances
that canonical list manipulating operations like `head`, `tail`, `foldl1`
and (incomplete) pattern matches will not *blow up* at run-time.

<!-- more -->


<pre><span class=hs-linenum>26: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>ListLengths</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>27: </span>
<span class=hs-linenum>28: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>length</span><span class='hs-layout'>,</span> <span class='hs-varid'>map</span><span class='hs-layout'>,</span> <span class='hs-varid'>filter</span><span class='hs-layout'>,</span> <span class='hs-varid'>head</span><span class='hs-layout'>,</span> <span class='hs-varid'>tail</span><span class='hs-layout'>,</span> <span class='hs-varid'>foldl1</span><span class='hs-layout'>)</span>
<span class=hs-linenum>29: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span> <span class='hs-layout'>(</span><span class='hs-varid'>liquidError</span><span class='hs-layout'>)</span>
<span class=hs-linenum>30: </span><span class='hs-keyword'>import</span> <span class='hs-keyword'>qualified</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>HashMap</span><span class='hs-varop'>.</span><span class='hs-conid'>Strict</span> <span class='hs-keyword'>as</span> <span class='hs-conid'>M</span>
<span class=hs-linenum>31: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Hashable</span> 
</pre>

Measuring the Length of a List
------------------------------

To begin, we need some instrument by which to measure the length of a list.
To this end, let's introduce a new mechanism called **measures** which 
define auxiliary (or so-called **ghost**) properties of data values.
These properties are useful for specification and verification, but
**don't actually exist at run-time**.
That is, measures will appear in specifications but *never* inside code.




 Let's reuse this mechanism, this time, providing a [definition](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/known-packages/base/GHC.Base.spec) for the measure
<pre><span class=hs-linenum>48: </span><span class='hs-definition'>measure</span> <span class='hs-varid'>len</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span><span class='hs-varop'>.</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>GHC</span><span class='hs-varop'>.</span><span class='hs-conid'>Types</span><span class='hs-varop'>.</span><span class='hs-conid'>Int</span>
<span class=hs-linenum>49: </span><span class='hs-definition'>len</span> <span class='hs-layout'>(</span><span class='hs-conid'>[]</span><span class='hs-layout'>)</span>     <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span>
<span class=hs-linenum>50: </span><span class='hs-definition'>len</span> <span class='hs-layout'>(</span><span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>ys</span><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span> 
</pre>

The description of `len` above should be quite easy to follow. Underneath the 
covers, LiquidHaskell transforms the above description into refined versions 
of the types for the constructors `(:)` and `[]`,
Something like 
<pre><span class=hs-linenum>57: </span><span class='hs-keyword'>data</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>where</span> 
<span class=hs-linenum>58: </span>  <span class='hs-conid'>[]</span>  <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span><span class='hs-varop'>.</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span> <span class='hs-layout'>}</span>
<span class=hs-linenum>59: </span>  <span class='hs-layout'>(</span><span class='hs-conop'>:</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span><span class='hs-varop'>.</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span> <span class='hs-layout'>}</span> 
</pre>

To appreciate this, note that we can now check that


<pre><span class=hs-linenum>65: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>xs</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>String</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (len v) = 1 }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>66: </span><a class=annot href="#"><span class=annottext>{VV : [[(GHC.Types.Char)]] | (len([VV]) = 1)}</span><span class='hs-definition'>xs</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"dog"</span></a> <a class=annot href="#"><span class=annottext>y:{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}
-&gt; ys:[{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}]
-&gt; {VV : [{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : [{VV : (GHC.Types.Char) | false}] | false}] | (len([VV]) = 0),
                                                           (len([VV]) &gt;= 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>67: </span>
<span class=hs-linenum>68: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>ys</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>String</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (len v) = 2 }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>69: </span><a class=annot href="#"><span class=annottext>{VV : [[(GHC.Types.Char)]] | (len([VV]) = 2)}</span><span class='hs-definition'>ys</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}] | (len([VV]) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"cat"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"dog"</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>70: </span>
<span class=hs-linenum>71: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>zs</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>String</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (len v) = 3 }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>72: </span><a class=annot href="#"><span class=annottext>{VV : [[(GHC.Types.Char)]] | (len([VV]) = 3)}</span><span class='hs-definition'>zs</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"hippo"</span></a> <a class=annot href="#"><span class=annottext>y:[(GHC.Types.Char)]
-&gt; ys:[[(GHC.Types.Char)]]
-&gt; {VV : [[(GHC.Types.Char)]] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : [[(GHC.Types.Char)]] | (VV = ys),
                             (len([VV]) = 2),
                             (len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
</pre>

Dually, when we *de-construct* the lists, LiquidHaskell is able to relate
the type of the outer list with its constituents. For example,


<pre><span class=hs-linenum>79: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>zs'</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>String</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (len v) = 2 }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>80: </span><a class=annot href="#"><span class=annottext>{VV : [[(GHC.Types.Char)]] | (len([VV]) = 2)}</span><span class='hs-definition'>zs'</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>case</span> <a class=annot href="#"><span class=annottext>{VV : [[(GHC.Types.Char)]] | (VV = zs),
                             (len([VV]) = 3),
                             (len([VV]) &gt;= 0)}</span><span class='hs-varid'>zs</span></a> <span class='hs-keyword'>of</span> 
<span class=hs-linenum>81: </span>        <span class='hs-varid'>h</span> <span class='hs-conop'>:</span> <span class='hs-varid'>t</span> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{VV : [[(GHC.Types.Char)]] | (VV = t),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>t</span></a>
</pre>

Here, from the use of the `:` in the pattern, LiquidHaskell can determine
that `(len zs) = 1 + (len t)`; by combining this fact with the nugget
that `(len zs) = 3` LiquidHaskell concludes that `t`, and hence, `zs'`
contains two elements.

Reasoning about Lengths
-----------------------

Let's flex our new vocabulary by uttering types that describe the
behavior of the usual list functions. 

First up: a version of the [standard][ghclist] 
`length` function, slightly simplified for exposition.


<pre><span class=hs-linenum>99: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>length</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = (len xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>100: </span><span class='hs-definition'>length</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>101: </span><a class=annot href="#"><span class=annottext>xs:[a] -&gt; {VV : (GHC.Types.Int) | (VV = len([xs]))}</span><span class='hs-definition'>length</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(GHC.Prim.Int#) -&gt; {VV : (GHC.Types.Int) | (VV = (x  :  int))}</span><span class='hs-num'>0</span></a>
<span class=hs-linenum>102: </span><span class='hs-definition'>length</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>xs:[a] -&gt; {VV : (GHC.Types.Int) | (VV = len([xs]))}</span><span class='hs-varid'>length</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

**Note:** Recall that `measure` values don't actually exist at run-time.
However, functions like `length` are useful in that they allow us to
effectively *pull* or *materialize* the ghost values from the refinement
world into the actual code world (since the value returned by `length` is
logically equal to the `len` of the input list.)

Similarly, we can speak and have confirmed, the types for the usual
list-manipulators like


<pre><span class=hs-linenum>115: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>map</span>      <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>b</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (len v) = (len xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>116: </span><a class=annot href="#"><span class=annottext>(a -&gt; b)
-&gt; x1:[a] -&gt; {VV : [b] | (len([VV]) = len([x1])),(len([VV]) &gt;= 0)}</span><span class='hs-definition'>map</span></a> <span class='hs-keyword'>_</span> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}] | (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a> 
<span class=hs-linenum>117: </span><span class='hs-definition'>map</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>y:a -&gt; ys:[a] -&gt; {VV : [a] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(a -&gt; b)
-&gt; x1:[a] -&gt; {VV : [b] | (len([VV]) = len([x1])),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>map</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
</pre>

and


<pre><span class=hs-linenum>123: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>filter</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (len v) &lt;= (len xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>124: </span><a class=annot href="#"><span class=annottext>(a -&gt; (GHC.Types.Bool))
-&gt; x1:[a] -&gt; {VV : [a] | (len([VV]) &gt;= 0),(len([VV]) &lt;= len([x1]))}</span><span class='hs-definition'>filter</span></a> <span class='hs-keyword'>_</span> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}] | (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>125: </span><span class='hs-definition'>filter</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>126: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>y:a -&gt; ys:[a] -&gt; {VV : [a] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>(a -&gt; (GHC.Types.Bool))
-&gt; x1:[a] -&gt; {VV : [a] | (len([VV]) &gt;= 0),(len([VV]) &lt;= len([x1]))}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>127: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(a -&gt; (GHC.Types.Bool))
-&gt; x1:[a] -&gt; {VV : [a] | (len([VV]) &gt;= 0),(len([VV]) &lt;= len([x1]))}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

and, since doubtless you are wondering,


<pre><span class=hs-linenum>133: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>append</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (len v) = (len xs) + (len ys)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>134: </span><a class=annot href="#"><span class=annottext>x4:[a]
-&gt; x3:[a]
-&gt; {VV : [a] | (len([VV]) = (len([x4]) + len([x3]))),
               (len([VV]) = (len([x3]) + len([x4]))),
               (len([VV]) &gt;= 0)}</span><span class='hs-definition'>append</span></a> <span class='hs-conid'>[]</span> <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>ys</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a> 
<span class=hs-linenum>135: </span><span class='hs-definition'>append</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varid'>ys</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>y:a -&gt; ys:[a] -&gt; {VV : [a] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>x4:[a]
-&gt; x3:[a]
-&gt; {VV : [a] | (len([VV]) = (len([x4]) + len([x3]))),
               (len([VV]) = (len([x3]) + len([x4]))),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>append</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
</pre>

We will return to the above at some later date. Right now, let's look at
some interesting programs that LiquidHaskell can prove safe, by reasoning
about the size of various lists.



Example 1: Safely Catching A List by Its Tail (or Head) 
-------------------------------------------------------

Now, let's see how we can use these new incantations to banish, forever,
certain irritating kinds of errors. 
Recall how we always summon functions like `head` and `tail` with a degree of trepidation, unsure whether the arguments are empty, which will awaken certain beasts
<pre><span class=hs-linenum>150: </span><span class='hs-conid'>Prelude</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>head</span> <span class='hs-conid'>[]</span>
<span class=hs-linenum>151: </span><span class='hs-varop'>***</span> <span class='hs-conid'>Exception</span><span class='hs-conop'>:</span> <span class='hs-conid'>Prelude</span><span class='hs-varop'>.</span><span class='hs-varid'>head</span><span class='hs-conop'>:</span> <span class='hs-varid'>empty</span> <span class='hs-varid'>list</span>
</pre>

LiquidHaskell allows us to use these functions with 
confidence and surety! First off, let's define a predicate
alias that describes non-empty lists:


<pre><span class=hs-linenum>159: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>NonNull</span> <span class='hs-conid'>X</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span> <span class='hs-varop'>&gt;</span> <span class='hs-num'>0</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>

Now, we can type the potentially dangerous `head` as:


<pre><span class=hs-linenum>165: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>head</span>   <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (NonNull v)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>166: </span><a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt; 0)} -&gt; a</span><span class='hs-definition'>head</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>167: </span><span class='hs-definition'>head</span> <span class='hs-conid'>[]</span>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | false} -&gt; {VV : a | false}</span><span class='hs-varid'>liquidError</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"Fear not! 'twill ne'er come to pass"</span></a>
</pre>

As with the case of [divide-by-zero][ref101], LiquidHaskell deduces that
the second equation is *dead code* since the precondition (input) type
states that the length of the input is strictly positive, which *precludes*
the case where the parameter is `[]`.

Similarly, we can write


<pre><span class=hs-linenum>178: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>tail</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (NonNull v)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>179: </span><a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt; 0)} -&gt; [a]</span><span class='hs-definition'>tail</span></a> <span class='hs-layout'>(</span><span class='hs-keyword'>_</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>180: </span><span class='hs-definition'>tail</span> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | false}
-&gt; {VV : [{VV : a | false}] | false}</span><span class='hs-varid'>liquidError</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"Relaxeth! this too shall ne'er be"</span></a>
</pre>

Once again, LiquidHaskell will use the precondition to verify that the 
`liquidError` is never invoked. 

Let's use the above to write a function that eliminates stuttering, that
is which converts `"ssstringssss liiiiiike thisss"` to `"strings like this"`.


<pre><span class=hs-linenum>190: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>eliminateStutter</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Eq</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>191: </span><a class=annot href="#"><span class=annottext>(GHC.Classes.Eq a) -&gt; [a] -&gt; [a]</span><span class='hs-definition'>eliminateStutter</span></a> <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>xs</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>({VV : [a] | (len([VV]) &gt; 0)} -&gt; a)
-&gt; xs:[{VV : [a] | (len([VV]) &gt; 0)}]
-&gt; {VV : [a] | (len([VV]) = len([xs]))}</span><span class='hs-varid'>map</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt; 0)} -&gt; a</span><span class='hs-varid'>head</span></a> <a class=annot href="#"><span class=annottext>({VV : [{VV : [a] | (len([VV]) &gt; 0)}] | ((len([xs]) &gt; 0) =&gt; (len([VV]) &gt; 0)),
                                        (len([VV]) &gt;= 0)}
 -&gt; {VV : [a] | (len([VV]) &gt;= 0)})
-&gt; {VV : [{VV : [a] | (len([VV]) &gt; 0)}] | ((len([xs]) &gt; 0) =&gt; (len([VV]) &gt; 0)),
                                          (len([VV]) &gt;= 0)}
-&gt; {VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>x1:{VV : [a] | (len([VV]) &gt;= 0)}
-&gt; {VV : [{VV : [a] | (len([VV]) &gt; 0)}] | ((len([x1]) &gt; 0) =&gt; (len([VV]) &gt; 0)),
                                          (len([VV]) &gt;= 0)}</span><span class='hs-varid'>groupEq</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> 
</pre>

The heavy lifting is done by `groupEq`


<pre><span class=hs-linenum>197: </span><a class=annot href="#"><span class=annottext>x1:{VV : [a] | (len([VV]) &gt;= 0)}
-&gt; {VV : [{VV : [a] | (len([VV]) &gt; 0)}] | ((len([x1]) &gt; 0) =&gt; (len([VV]) &gt; 0)),
                                          (len([VV]) &gt;= 0)}</span><span class='hs-definition'>groupEq</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [{VV : a | false}] | false}] | (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>198: </span><span class='hs-definition'>groupEq</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>y:a -&gt; ys:[a] -&gt; {VV : [a] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),
            (VV = ys),
            (len([VV]) = len([ys])),
            (len([VV]) &gt;= 0),
            (len([VV]) &lt;= len([ys]))}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>y:{VV : [a] | (len([VV]) &gt; 0)}
-&gt; ys:[{VV : [a] | (len([VV]) &gt; 0)}]
-&gt; {VV : [{VV : [a] | (len([VV]) &gt; 0)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>x1:{VV : [a] | (len([VV]) &gt;= 0)}
-&gt; {VV : [{VV : [a] | (len([VV]) &gt; 0)}] | ((len([x1]) &gt; 0) =&gt; (len([VV]) &gt; 0)),
                                          (len([VV]) &gt;= 0)}</span><span class='hs-varid'>groupEq</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = zs),
            (VV = zs),
            (len([VV]) = len([zs])),
            (len([VV]) &gt;= 0),
            (len([VV]) &lt;= len([zs]))}</span><span class='hs-varid'>zs</span></a>
<span class=hs-linenum>199: </span>                 <span class='hs-keyword'>where</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),
            (len([VV]) = len([ys])),
            (len([VV]) &gt;= 0),
            (len([VV]) &lt;= len([ys]))}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = zs),
            (len([VV]) = len([zs])),
            (len([VV]) &gt;= 0),
            (len([VV]) &lt;= len([zs]))}</span><span class='hs-varid'>zs</span></a><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(a -&gt; (GHC.Types.Bool)) -&gt; [a] -&gt; ([a] , [a])</span><span class='hs-varid'>span</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:a
-&gt; y:a -&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x = y))}</span><span class='hs-varop'>==</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

which gathers consecutive equal elements in the list into a single list.
By using the fact that *each element* in the output returned by 
`groupEq` is in fact of the form `x:ys`, LiquidHaskell infers that
`groupEq` returns a *list of non-empty lists*. 
(Hover over the `groupEq` identifier in the code above to see this.)
Next, by automatically instantiating the type parameter for the `map` 
in `eliminateStutter` to `(len v) > 0` LiquidHaskell deduces `head` 
is only called on non-empty lists, thereby verifying the safety of 
`eliminateStutter`. (Hover your mouse over `map` above to see the
instantiated type for it!)

Example 2: Risers 
-----------------

The above examples of `head` and `tail` are simple, but non-empty lists pop
up in many places, and it is rather convenient to have the type system
track non-emptiness without having to make up special types. Let's look at a
more interesting example, popularized by [Neil Mitchell][risersMitchell]
which is a key step in an efficient sorting procedure, which we may return
to in the future when we discuss sorting algorithms.


<pre><span class=hs-linenum>224: </span><span class='hs-definition'>risers</span>           <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>225: </span><a class=annot href="#"><span class=annottext>(GHC.Classes.Ord a)
-&gt; zs:[a] -&gt; {VV : [[a]] | ((len([zs]) &gt; 0) =&gt; (len([VV]) &gt; 0))}</span><span class='hs-definition'>risers</span></a> <span class='hs-conid'>[]</span>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [{VV : a | false}] | false}] | (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>226: </span><span class='hs-definition'>risers</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [{VV : a | false}] | false}] | (len([VV]) = 0),
                                            (len([VV]) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV = x)}] | (len([VV]) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>227: </span><span class='hs-definition'>risers</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>etc</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}] | (len([VV]) = 0),(len([VV]) &gt;= 0)}</span><span class='hs-keyword'>if</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:a
-&gt; y:a -&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyword'>then</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>y:a -&gt; ys:[a] -&gt; {VV : [a] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = s),
            (VV = s),
            (len([VV]) = len([s])),
            (len([VV]) &gt;= 0),
            (len([VV]) &lt;= len([s]))}</span><span class='hs-varid'>s</span></a><span class='hs-layout'>)</span><a class=annot href="#"><span class=annottext>y:[a] -&gt; ys:[[a]] -&gt; {VV : [[a]] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [[a]] | (VV = ss),
              (VV = ss),
              (len([VV]) = len([ss])),
              (len([VV]) &gt;= 0),
              (len([VV]) &lt;= len([ss]))}</span><span class='hs-varid'>ss</span></a> <span class='hs-keyword'>else</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV = x),(VV &gt; y)}] | (len([VV]) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span><a class=annot href="#"><span class=annottext>y:[a] -&gt; ys:[[a]] -&gt; {VV : [[a]] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a><span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = s),
            (VV = s),
            (len([VV]) = len([s])),
            (len([VV]) &gt;= 0),
            (len([VV]) &lt;= len([s]))}</span><span class='hs-varid'>s</span></a><a class=annot href="#"><span class=annottext>y:[a] -&gt; ys:[[a]] -&gt; {VV : [[a]] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [[a]] | (VV = ss),
              (VV = ss),
              (len([VV]) = len([ss])),
              (len([VV]) &gt;= 0),
              (len([VV]) &lt;= len([ss]))}</span><span class='hs-varid'>ss</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>228: </span>    <span class='hs-keyword'>where</span> 
<span class=hs-linenum>229: </span>      <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = s),
            (len([VV]) = len([s])),
            (len([VV]) &gt;= 0),
            (len([VV]) &lt;= len([s]))}</span><span class='hs-varid'>s</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [[a]] | (VV = ss),
              (len([VV]) = len([ss])),
              (len([VV]) &gt;= 0),
              (len([VV]) &lt;= len([ss]))}</span><span class='hs-varid'>ss</span></a><span class='hs-layout'>)</span>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [[a]] | (len([VV]) &gt; 0)}
-&gt; ([a] , {VV : [[a]] | (len([VV]) &gt;= 0)})</span><span class='hs-varid'>safeSplit</span></a> <a class=annot href="#"><span class=annottext>({VV : [[a]] | ((len([etc]) &gt; 0) =&gt; (len([VV]) &gt; 0)),
               (len([VV]) &gt; 0)}
 -&gt; ([a] , {VV : [[a]] | (len([VV]) &gt;= 0)}))
-&gt; {VV : [[a]] | ((len([etc]) &gt; 0) =&gt; (len([VV]) &gt; 0)),
                 (len([VV]) &gt; 0)}
-&gt; ([a] , {VV : [[a]] | (len([VV]) &gt;= 0)})</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>zs:[a] -&gt; {VV : [[a]] | ((len([zs]) &gt; 0) =&gt; (len([VV]) &gt; 0))}</span><span class='hs-varid'>risers</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a><a class=annot href="#"><span class=annottext>y:a -&gt; ys:[a] -&gt; {VV : [a] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = etc),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>etc</span></a><span class='hs-layout'>)</span>
</pre>

The bit that should cause some worry is `safeSplit` which 
simply returns the `head` and `tail` of its input, if they
exist, and otherwise, crashes and burns


<pre><span class=hs-linenum>237: </span><a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt; 0)} -&gt; (a , {VV : [a] | (len([VV]) &gt;= 0)})</span><span class='hs-definition'>safeSplit</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:a -&gt; b -&gt; (a , b)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>238: </span><span class='hs-definition'>safeSplit</span> <span class='hs-keyword'>_</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | false}
-&gt; {VV : ({VV : a | false} , {VV : [{VV : a | false}] | false}) | false}</span><span class='hs-varid'>liquidError</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"don't worry, be happy"</span></a>
</pre>

How can we verify that `safeSplit` *will not crash* ?

The matter is complicated by the fact that since `risers` 
*does* sometimes return an empty list, we cannot blithely 
specify that its output type has a `NonNull` refinement.

Once again, logic rides to our rescue!

The crucial property upon which the safety of `risers` rests
is that when the input list is non-empty, the output list 
returned by risers is *also* non-empty. It is quite easy to clue 
LiquidHaskell in on this, namely through a type specification:


<pre><span class=hs-linenum>255: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>risers</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>256: </span>           <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>zs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> 
<span class=hs-linenum>257: </span>           <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-keyglyph'>[</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| ((NonNull zs) =&gt; (NonNull v)) }</span> <span class='hs-keyword'>@-}</span> 
</pre>

Note how we relate the output's non-emptiness to the input's
non-emptiness,through the (dependent) refinement type. With this 
specification in place, LiquidHaskell is pleased to verify `risers` 
(i.e. the call to `safeSplit`).

Example 3: MapReduce 
--------------------

Here's a longer example that illustrates this: a toy *map-reduce* implementation.

First, let's write a function `keyMap` that expands a list of inputs into a 
list of key-value pairs:


<pre><span class=hs-linenum>274: </span><span class='hs-definition'>keyMap</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-varid'>k</span><span class='hs-layout'>,</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-varid'>k</span><span class='hs-layout'>,</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>275: </span><a class=annot href="#"><span class=annottext>(a -&gt; {VV : [(b , c)] | (len([VV]) &gt;= 0)}) -&gt; [a] -&gt; [(b , c)]</span><span class='hs-definition'>keyMap</span></a> <a class=annot href="#"><span class=annottext>a -&gt; {VV : [(b , c)] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>xs</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(a -&gt; [(b , c)]) -&gt; [a] -&gt; [(b , c)]</span><span class='hs-varid'>concatMap</span></a> <a class=annot href="#"><span class=annottext>a -&gt; {VV : [(b , c)] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

Next, let's write a function `group` that gathers the key-value pairs into a
`Map` from *keys* to the lists of values with that same key.


<pre><span class=hs-linenum>282: </span><a class=annot href="#"><span class=annottext>(GHC.Classes.Eq a)
-&gt; (Data.Hashable.Class.Hashable a)
-&gt; [(a , b)]
-&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})</span><span class='hs-definition'>group</span></a> <a class=annot href="#"><span class=annottext>[(a , b)]</span><span class='hs-varid'>kvs</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>((a , b)
 -&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})
 -&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)}))
-&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})
-&gt; [(a , b)]
-&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})</span><span class='hs-varid'>foldr</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(a , b)
-&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})
-&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})</span><span class='hs-keyglyph'>\</span></a><span class='hs-layout'>(</span><span class='hs-varid'>k</span><span class='hs-layout'>,</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>(Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})</span><span class='hs-varid'>m</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>a
-&gt; b
-&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})
-&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})</span><span class='hs-varid'>inserts</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = k)}</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = v)}</span><span class='hs-varid'>v</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)}) | (VV = m)}</span><span class='hs-varid'>m</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>(Data.HashMap.Base.HashMap {VV : a | false} {VV : [{VV : b | false}] | false})</span><span class='hs-conid'>M</span></a><span class='hs-varop'>.</span><span class='hs-varid'>empty</span> <a class=annot href="#"><span class=annottext>{VV : [(a , b)] | (VV = kvs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>kvs</span></a> 
</pre>

The function `inserts` simply adds the new value `v` to the list of 
previously known values `lookupDefault [] k m` for the key `k`.


<pre><span class=hs-linenum>289: </span><a class=annot href="#"><span class=annottext>(GHC.Classes.Eq a)
-&gt; (Data.Hashable.Class.Hashable a)
-&gt; a
-&gt; b
-&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})
-&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})</span><span class='hs-definition'>inserts</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>v</span></a> <a class=annot href="#"><span class=annottext>(Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})</span><span class='hs-varid'>m</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a
-&gt; {VV : [b] | (len([VV]) &gt; 0)}
-&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})
-&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})</span><span class='hs-conid'>M</span></a><span class='hs-varop'>.</span><span class='hs-varid'>insert</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = k)}</span><span class='hs-varid'>k</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = v)}</span><span class='hs-varid'>v</span></a> <a class=annot href="#"><span class=annottext>y:a -&gt; ys:[a] -&gt; {VV : [a] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = vs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>vs</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)}) | (VV = m)}</span><span class='hs-varid'>m</span></a> 
<span class=hs-linenum>290: </span>  <span class='hs-keyword'>where</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>vs</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt;= 0)}
-&gt; b
-&gt; (Data.HashMap.Base.HashMap b {VV : [a] | (len([VV]) &gt;= 0)})
-&gt; {VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-conid'>M</span></a><span class='hs-varop'>.</span><span class='hs-varid'>lookupDefault</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}] | (len([VV]) = 0),(len([VV]) &gt;= 0)}</span><span class='hs-conid'>[]</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = k)}</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)}) | (VV = m)}</span><span class='hs-varid'>m</span></a>
</pre>

Finally, a function that *reduces* the list of values for a given
key in the table to a single value:


<pre><span class=hs-linenum>297: </span><span class='hs-definition'>reduce</span>    <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>M</span><span class='hs-varop'>.</span><span class='hs-conid'>HashMap</span> <span class='hs-varid'>k</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>v</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>M</span><span class='hs-varop'>.</span><span class='hs-conid'>HashMap</span> <span class='hs-varid'>k</span> <span class='hs-varid'>v</span>
<span class=hs-linenum>298: </span><a class=annot href="#"><span class=annottext>(x2:a -&gt; x3:a -&gt; {VV : a | (VV &gt; x2),(VV &gt; x3)})
-&gt; (Data.HashMap.Base.HashMap b {VV : [a] | (len([VV]) &gt; 0)})
-&gt; (Data.HashMap.Base.HashMap b a)</span><span class='hs-definition'>reduce</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; x2:a -&gt; {VV : a | (VV &gt; x1),(VV &gt; x2)}</span><span class='hs-varid'>op</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>({VV : [a] | (len([VV]) &gt; 0)} -&gt; a)
-&gt; (Data.HashMap.Base.HashMap b {VV : [a] | (len([VV]) &gt; 0)})
-&gt; (Data.HashMap.Base.HashMap b a)</span><span class='hs-conid'>M</span></a><span class='hs-varop'>.</span><span class='hs-varid'>map</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(a -&gt; a -&gt; a) -&gt; {VV : [a] | (len([VV]) &gt; 0)} -&gt; a</span><span class='hs-varid'>foldl1</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; x2:a -&gt; {VV : a | (VV &gt; x1),(VV &gt; x2)}</span><span class='hs-varid'>op</span></a><span class='hs-layout'>)</span>
</pre>

where `foldl1` is a [left-fold over *non-empty* lists][foldl1]


<pre><span class=hs-linenum>304: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>foldl1</span>      <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (NonNull v)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>305: </span><a class=annot href="#"><span class=annottext>(a -&gt; a -&gt; a) -&gt; {VV : [a] | (len([VV]) &gt; 0)} -&gt; a</span><span class='hs-definition'>foldl1</span></a> <a class=annot href="#"><span class=annottext>a -&gt; a -&gt; a</span><span class='hs-varid'>f</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span>  <a class=annot href="#"><span class=annottext>(a -&gt; a -&gt; a) -&gt; a -&gt; [a] -&gt; a</span><span class='hs-varid'>foldl</span></a> <a class=annot href="#"><span class=annottext>a -&gt; a -&gt; a</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>306: </span><span class='hs-definition'>foldl1</span> <span class='hs-keyword'>_</span> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span>  <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | false} -&gt; {VV : a | false}</span><span class='hs-varid'>liquidError</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"will. never. happen."</span></a>
</pre>

We can put the whole thing together to write a (*very*) simple *Map-Reduce* library


<pre><span class=hs-linenum>312: </span><span class='hs-definition'>mapReduce</span>   <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Eq</span> <span class='hs-varid'>k</span><span class='hs-layout'>,</span> <span class='hs-conid'>Hashable</span> <span class='hs-varid'>k</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>313: </span>            <span class='hs-keyglyph'>=&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-varid'>k</span><span class='hs-layout'>,</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span><span class='hs-layout'>)</span>    <span class='hs-comment'>-- ^ key-mapper</span>
<span class=hs-linenum>314: </span>            <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span>      <span class='hs-comment'>-- ^ reduction operator</span>
<span class=hs-linenum>315: </span>            <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>                <span class='hs-comment'>-- ^ inputs</span>
<span class=hs-linenum>316: </span>            <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-varid'>k</span><span class='hs-layout'>,</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span>           <span class='hs-comment'>-- ^ output key-values</span>
<span class=hs-linenum>317: </span>
<span class=hs-linenum>318: </span><a class=annot href="#"><span class=annottext>(GHC.Classes.Eq a)
-&gt; (Data.Hashable.Class.Hashable a)
-&gt; (b -&gt; {VV : [(a , c)] | (len([VV]) &gt;= 0)})
-&gt; (x7:c -&gt; x8:c -&gt; {VV : c | (VV &gt; x7),(VV &gt; x8)})
-&gt; [b]
-&gt; [(a , c)]</span><span class='hs-definition'>mapReduce</span></a> <a class=annot href="#"><span class=annottext>a -&gt; {VV : [(b , c)] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; x2:a -&gt; {VV : a | (VV &gt; x1),(VV &gt; x2)}</span><span class='hs-varid'>op</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(Data.HashMap.Base.HashMap a b) -&gt; [(a , b)]</span><span class='hs-conid'>M</span></a><span class='hs-varop'>.</span><span class='hs-varid'>toList</span> 
<span class=hs-linenum>319: </span>                <a class=annot href="#"><span class=annottext>((Data.HashMap.Base.HashMap a b) -&gt; [(a , b)])
-&gt; ([c] -&gt; (Data.HashMap.Base.HashMap a b)) -&gt; [c] -&gt; [(a , b)]</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>(x2:a -&gt; x3:a -&gt; {VV : a | (VV &gt; x2),(VV &gt; x3)})
-&gt; (Data.HashMap.Base.HashMap b {VV : [a] | (len([VV]) &gt; 0)})
-&gt; (Data.HashMap.Base.HashMap b a)</span><span class='hs-varid'>reduce</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; x2:a -&gt; {VV : a | (VV &gt; x1),(VV &gt; x2)}</span><span class='hs-varid'>op</span></a> 
<span class=hs-linenum>320: </span>                <a class=annot href="#"><span class=annottext>((Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})
 -&gt; (Data.HashMap.Base.HashMap a b))
-&gt; ([c]
    -&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)}))
-&gt; [c]
-&gt; (Data.HashMap.Base.HashMap a b)</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>[(a , b)]
-&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})</span><span class='hs-varid'>group</span></a> 
<span class=hs-linenum>321: </span>                <a class=annot href="#"><span class=annottext>([(a , b)]
 -&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)}))
-&gt; ([c] -&gt; [(a , b)])
-&gt; [c]
-&gt; (Data.HashMap.Base.HashMap a {VV : [b] | (len([VV]) &gt; 0)})</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>(a -&gt; {VV : [(b , c)] | (len([VV]) &gt;= 0)}) -&gt; [a] -&gt; [(b , c)]</span><span class='hs-varid'>keyMap</span></a> <a class=annot href="#"><span class=annottext>a -&gt; {VV : [(b , c)] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>f</span></a>
</pre>

Now, if we want to compute the frequency of `Char` in a given list of words, we can write:


<pre><span class=hs-linenum>327: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>charFrequency</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>String</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-conid'>Char</span><span class='hs-layout'>,</span> <span class='hs-conid'>Int</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>328: </span><span class='hs-definition'>charFrequency</span>     <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>String</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-conid'>Char</span><span class='hs-layout'>,</span> <span class='hs-conid'>Int</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>329: </span><a class=annot href="#"><span class=annottext>[[(GHC.Types.Char)]] -&gt; [((GHC.Types.Char) , (GHC.Types.Int))]</span><span class='hs-definition'>charFrequency</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>([(GHC.Types.Char)]
 -&gt; {VV : [((GHC.Types.Char) , {VV : (GHC.Types.Int) | (VV &gt; 0)})] | (len([VV]) &gt;= 0)})
-&gt; (x8:{VV : (GHC.Types.Int) | (VV &gt; 0)}
    -&gt; x9:{VV : (GHC.Types.Int) | (VV &gt; 0)}
    -&gt; {VV : (GHC.Types.Int) | (VV &gt; 0),(VV &gt; x8),(VV &gt; x9)})
-&gt; [[(GHC.Types.Char)]]
-&gt; [((GHC.Types.Char) , {VV : (GHC.Types.Int) | (VV &gt; 0)})]</span><span class='hs-varid'>mapReduce</span></a> <a class=annot href="#"><span class=annottext>x1:[(GHC.Types.Char)]
-&gt; {VV : [((GHC.Types.Char) , {VV : (GHC.Types.Int) | (VV = 1),
                                                      (VV = len([xs])),
                                                      (VV &gt; 0)})] | (len([VV]) = len([x1])),
                                                                    (len([VV]) &gt;= 0)}</span><span class='hs-varid'>wordChars</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x + y))}</span><span class='hs-layout'>(</span></a><span class='hs-varop'>+</span><span class='hs-layout'>)</span>
<span class=hs-linenum>330: </span>  <span class='hs-keyword'>where</span> <a class=annot href="#"><span class=annottext>x1:[a]
-&gt; {VV : [(a , {VV : (GHC.Types.Int) | (VV = 1),
                                       (VV = len([xs])),
                                       (VV &gt; 0)})] | (len([VV]) = len([x1])),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>wordChars</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(a
 -&gt; (a , {VV : (GHC.Types.Int) | (VV = 1),
                                 (VV = len([xs])),
                                 (VV &gt; 0)}))
-&gt; xs:[a]
-&gt; {VV : [(a , {VV : (GHC.Types.Int) | (VV = 1),
                                       (VV = len([xs])),
                                       (VV &gt; 0)})] | (len([VV]) = len([xs]))}</span><span class='hs-varid'>map</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>c:a
-&gt; ({VV : a | (VV = c)} , {VV : (GHC.Types.Int) | (VV = 1),
                                                  (VV = len([xs])),
                                                  (VV &gt; 0)})</span><span class='hs-keyglyph'>\</span></a><a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>c</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>x1:a -&gt; b -&gt; (a , b)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV = c)}</span><span class='hs-varid'>c</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span> 
</pre>

You can take it out for a spin like so:


<pre><span class=hs-linenum>336: </span><a class=annot href="#"><span class=annottext>[((GHC.Types.Char) , (GHC.Types.Int))]</span><span class='hs-definition'>f0</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[[(GHC.Types.Char)]] -&gt; [((GHC.Types.Char) , (GHC.Types.Int))]</span><span class='hs-varid'>charFrequency</span></a> <span class='hs-keyglyph'>[</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"the"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"quick"</span></a> <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"brown"</span></a>
<span class=hs-linenum>337: </span>                   <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"fox"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"jumped"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"over"</span></a>
<span class=hs-linenum>338: </span>                   <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"the"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"lazy"</span></a>  <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"cow"</span></a>   <span class='hs-keyglyph'>]</span>
</pre>

**Look Ma! No Types:** LiquidHaskell will gobble the whole thing up, and
verify that none of the undesirable `liquidError` calls are triggered. By
the way, notice that we didn't write down any types for `mapReduce` and
friends.  The main invariant, from which safety follows is that the `Map`
returned by the `group` function binds each key to a *non-empty* list of
values.  LiquidHaskell deduces this invariant by inferring suitable types
for `group`, `inserts`, `foldl1` and `reduce`, thereby relieving us of that
tedium. In short, by riding on the broad and high shoulders of SMT and
abstract interpretation, LiquidHaskell makes a little typing go a long way. 


Conclusions
-----------

Well folks, thats all for now. I trust this article gave you a sense of

1. How we can describe certain *structural properties* of data types, 
   such as the length of a list, 

2. How we might use refinements over these properties to describe key
   invariants and establish, at compile-time, the safety of operations that
   might blow up on unexpected values at run-time, and perhaps, most
   importantly,

3. How we can achieve the above, whilst just working with good old lists, 
   without having to [make up new types][risersApple] (which have the 
   unfortunate effect of cluttering programs with their attendant new 
   functions) in order to enforce special invariants.


[vecbounds]:  /blog/2013/01/05/bounding-vectors.lhs/ 
[ghclist]:    https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/List.lhs#L125
[foldl1]:     http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#foldl1
[risersMitchell]: http://neilmitchell.blogspot.com/2008/03/sorting-at-speed.html
[risersApple]: http://blog.jbapple.com/2008/01/extra-type-safety-using-polymorphic.html
[ref101]:  /blog/2013/01/01/refinement-types-101.lhs/ 
[ref102]:  /blog/2013/01/27/refinements101-reax.lhs/ 

