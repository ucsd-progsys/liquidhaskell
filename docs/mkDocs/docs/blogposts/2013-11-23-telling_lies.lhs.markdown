---
layout: post
title: LiquidHaskell Caught Telling Lies!
date: 2013-11-23 16:12
comments: true
tags: termination
author: Ranjit Jhala and Niki Vazou 
published: true
demo: TellingLies.hs
---

One crucial goal of a type system is to provide the guarantee, 
memorably phrased by Milner as *well-typed programs don't go wrong*. 
The whole point of LiquidHaskell (and related systems) is to provide
the above guarantee for expanded notions of "going wrong". 
All this time, we've claimed (and believed) that LiquidHaskell 
provided such a guarantee.

We were wrong. 

LiquidHaskell tells lies.

<!-- more -->


<pre><span class=hs-linenum>27: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-termination"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>28: </span>
<span class=hs-linenum>29: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>TellingLies</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>30: </span>
<span class=hs-linenum>31: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span> <span class='hs-layout'>(</span><span class='hs-varid'>liquidError</span><span class='hs-layout'>)</span>
<span class=hs-linenum>32: </span>
<span class=hs-linenum>33: </span><span class='hs-definition'>divide</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>34: </span><span class='hs-definition'>foo</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>35: </span><span class='hs-definition'>explode</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
</pre>

To catch LiquidHaskell red-handed, we require

1. a notion of **going wrong**,
2. a **program** that clearly goes wrong, and the smoking gun,
3. a **lie** from LiquidHaskell that the program is safe.

The Going Wrong
---------------

Lets keep things simple with an old fashioned `div`-ision operator.
A division by zero would be, clearly *going wrong*.

To alert LiquidHaskell to this possibility, we encode "not going wrong"
with the precondition that the denominator be  non-zero.


<pre><span class=hs-linenum>54: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>divide</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>d</span><span class='hs-conop'>:</span><span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v /= 0}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>55: </span><a class=annot href="#"><span class=annottext>(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV /= 0)} -&gt; (GHC.Types.Int)</span><span class='hs-definition'>divide</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | false} -&gt; {VV : (GHC.Types.Int) | false}</span><span class='hs-varid'>liquidError</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0) &amp;&amp; ((sumLens VV) &gt;= 0)}</span><span class='hs-str'>"no you didn't!"</span></a>
<span class=hs-linenum>56: </span><span class='hs-definition'>divide</span> <span class='hs-varid'>n</span> <span class='hs-varid'>d</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == n)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (((x1 &gt;= 0) &amp;&amp; (x2 &gt;= 0)) =&gt; (VV &gt;= 0)) &amp;&amp; (((x1 &gt;= 0) &amp;&amp; (x2 &gt;= 1)) =&gt; (VV &lt;= x1)) &amp;&amp; (VV == (x1 / x2))}</span><span class='hs-varop'>`div`</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV /= 0)}</span><span class='hs-varid'>d</span></a>
</pre>

The Program 
-----------

Now, consider the function `foo`.


<pre><span class=hs-linenum>65: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>foo</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| v &lt; n}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>66: </span><a class=annot href="#"><span class=annottext>n:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; n)}</span><span class='hs-definition'>foo</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a> <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == n)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Bool) | (((Prop VV)) &lt;=&gt; (x1 &gt; x2))}</span><span class='hs-varop'>&gt;</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (0  :  int))}</span><span class='hs-num'>0</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == n)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV == (x1 - x2))}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (1  :  int))}</span><span class='hs-num'>1</span></a>
<span class=hs-linenum>67: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>n:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; n)}</span><span class='hs-varid'>foo</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == n)}</span><span class='hs-varid'>n</span></a>
</pre>

Now, `foo` should only be called with strictly positive values. 
In which case, the function returns a `Nat` that is strictly 
smaller than the input. 
The function diverges when called with `0` or negative inputs. 

Note that the signature of `foo` is slightly different, but 
nevertheless, legitimate, as *when* the function returns an 
output, the output is indeed a `Nat` that is *strictly less than* 
the input parameter `n`. Hence, LiquidHaskell happily checks 
that `foo` does indeed satisfy its given type.

So far, nothing has gone wrong either in the program, or 
with LiquidHaskell, but consider this innocent little 
function:


<pre><span class=hs-linenum>86: </span><a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-definition'>explode</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>let</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (0  :  int))}</span><span class='hs-varid'>z</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (0  :  int))}</span><span class='hs-num'>0</span></a>
<span class=hs-linenum>87: </span>          <span class='hs-keyword'>in</span>  <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x:{VV : (GHC.Types.Int) | (VV == 0) &amp;&amp; (VV == 1) &amp;&amp; (VV == TellingLies.explode) &amp;&amp; (VV == z) &amp;&amp; (VV &gt; 0) &amp;&amp; (VV &gt; TellingLies.explode) &amp;&amp; (VV &gt; z) &amp;&amp; (VV &lt; 0) &amp;&amp; (VV &lt; TellingLies.explode) &amp;&amp; (VV &lt; z)}
-&gt; {VV : (GHC.Types.Int) | (VV == 0) &amp;&amp; (VV == 1) &amp;&amp; (VV == TellingLies.explode) &amp;&amp; (VV == x) &amp;&amp; (VV == z) &amp;&amp; (VV &gt; 0) &amp;&amp; (VV &gt; TellingLies.explode) &amp;&amp; (VV &gt; x) &amp;&amp; (VV &gt; z) &amp;&amp; (VV &lt; 0) &amp;&amp; (VV &lt; TellingLies.explode) &amp;&amp; (VV &lt; x) &amp;&amp; (VV &lt; z)}</span><span class='hs-keyglyph'>\</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == 0) &amp;&amp; (VV == 1) &amp;&amp; (VV == TellingLies.explode) &amp;&amp; (VV == z) &amp;&amp; (VV &gt; 0) &amp;&amp; (VV &gt; TellingLies.explode) &amp;&amp; (VV &gt; z) &amp;&amp; (VV &lt; 0) &amp;&amp; (VV &lt; TellingLies.explode) &amp;&amp; (VV &lt; z)}</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (2013  :  int))}</span><span class='hs-num'>2013</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV /= 0)} -&gt; (GHC.Types.Int)</span><span class='hs-varop'>`divide`</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == z) &amp;&amp; (VV == (0  :  int))}</span><span class='hs-varid'>z</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>n:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; n)}</span><span class='hs-varid'>foo</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == z) &amp;&amp; (VV == (0  :  int))}</span><span class='hs-varid'>z</span></a><span class='hs-layout'>)</span>
</pre>

Thanks to *lazy evaluation*, the call to `foo` is ignored, so evaluating `explode` leads to a crash! Ugh!

The Lie
-------

However, LiquidHaskell produces a polyannish prognosis and 
cheerfully declares the program *safe*. 

Huh?

Well, LiquidHaskell deduces that

* `z == 0`  from the binding,
* `x : Nat` from the output type for `foo`
* `x <  z`  from the output type for `foo`

 Of course, no such `x` exists! Or, rather, the SMT solver reasons
<pre><span class=hs-linenum>108: </span>    <span class='hs-varid'>z</span> <span class='hs-varop'>==</span> <span class='hs-num'>0</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>x</span> <span class='hs-varop'>&gt;=</span> <span class='hs-num'>0</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>x</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>z</span>  <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>z</span> <span class='hs-varop'>/=</span> <span class='hs-num'>0</span>
</pre>

as the hypotheses are inconsistent. In other words, LiquidHaskell 
deduces that the call to `divide` happens in an *impossible* environment,
i.e. is dead code, and hence, the program is safe.

In our defence, the above, sunny prognosis is not *totally misguided*. 
Indeed, if Haskell was like ML and had *strict evaluation* then 
indeed the program would be safe in that we would *not* go wrong 
i.e. would not crash with a divide-by-zero.  

But of course, thats a pretty lame excuse, since Haskell doesn't have 
strict semantics. So looks like LiquidHaskell (and hence, we) 
have been caught red-handed.

Well then, is there a way to prevent LiquidHaskell from telling lies?
That is, can we get Milner's *well-typed programs don't go wrong* 
guarantee under lazy evaluation? 

Thankfully, there is.
