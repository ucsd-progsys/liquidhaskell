---
layout: post
title: Getting To the Bottom
date: 2013-12-02 16:12
comments: true
tags: termination
author: Ranjit Jhala and Niki Vazou
published: true 
demo: TellingLies.hs
---

[Previously][ref-lies], we caught LiquidHaskell telling a lie. Today, lets try to
get to the bottom of this mendacity, in order to understand how we can ensure
that it always tells the truth.

<!-- more -->


<pre><span class=hs-linenum>20: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>GettingToTheBottom</span> <span class='hs-keyword'>where</span>
</pre>

The Truth Lies At the Bottom
----------------------------

To figure out how we might prevent falsehoods, lets try to understand 
whats really going on. We need to go back to the beginning.

 Recall that the refinement type:
<pre><span class=hs-linenum>30: </span><span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-num'>0</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span>
</pre>

is supposed to denote the set of `Int` values that are greater than `0`.

 Consider a function:
<pre><span class=hs-linenum>36: </span><span class='hs-definition'>fib</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-num'>0</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>n</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-num'>0</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span>
<span class=hs-linenum>37: </span><span class='hs-definition'>fib</span> <span class='hs-varid'>n</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>e</span>
</pre>

Intuitively, the type signature states that when checking the body `e` 
we can **assume** that `0 <= n`. 

This is indeed the case with **strict** evaluation, as we are guaranteed 
that `n` will be evaluated before `e`. Thus, either:

1. `n` diverges and so we don't care about `e` as we won't evaluate it, or,
2. `n` is a non-negative value.

Thus, either way, `e` is only evaluated in a context where `0 <= n`.

But this is *not* the case with **lazy** evaluation, as we may 
well start evaluating `e` without evaluating `n`. Indeed, we may
*finish* evaluating `e` without evaluating `n`. 

Of course, *if* `n` is evaluated, it will yield a non-negative value, 
but if it is not (or does not) evaluate to a value, we **cannot assume** 
that the rest of the computation is dead (as with eager evaluation). 

 That is, with lazy evaluation, the refinement type `{n:Int | 0 <= n}` *actually* means:
<pre><span class=hs-linenum>60: </span><span class='hs-layout'>(</span><span class='hs-varid'>n</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>_</span><span class='hs-keyglyph'>|</span><span class='hs-keyword'>_</span><span class='hs-layout'>)</span> <span class='hs-varop'>||</span> <span class='hs-layout'>(</span><span class='hs-num'>0</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span>
</pre>

Keeping LiquidHaskell Honest
----------------------------

One approach to forcing LiquidHaskell to telling the truth is to force 
it to *always* split cases and reason about `_|_`.

 Lets revisit `explode`
<pre><span class=hs-linenum>70: </span><span class='hs-definition'>explode</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>let</span> <span class='hs-varid'>z</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span>
<span class=hs-linenum>71: </span>          <span class='hs-keyword'>in</span>  <span class='hs-layout'>(</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>x</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-num'>2013</span> <span class='hs-varop'>`divide`</span> <span class='hs-varid'>z</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>foo</span> <span class='hs-varid'>z</span><span class='hs-layout'>)</span>
</pre>

The case splitting prevents the cheerful but bogus prognosis that `explode` above was safe, because the SMT solver cannot prove that at the call to `divide` 
<pre><span class=hs-linenum>75: </span>    <span class='hs-varid'>z</span> <span class='hs-varop'>==</span> <span class='hs-num'>0</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>_</span><span class='hs-keyglyph'>|</span><span class='hs-keyword'>_</span> <span class='hs-varop'>||</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-varop'>&gt;=</span> <span class='hs-num'>0</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>x</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>z</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>  <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>z</span> <span class='hs-varop'>/=</span> <span class='hs-num'>0</span>
</pre>

But alas, this cure is worse than the disease. 
It would end up lobotomizing LiquidHaskell making it unable to prove even trivial things like:

_
<pre><span class=hs-linenum>82: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>trivial</span>    <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{pf:</span> <span class='hs-conid'>()</span> <span class='hs-keyword'>| x &lt; y}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>83: </span><span class='hs-definition'>trivial</span> <span class='hs-varid'>x</span> <span class='hs-varid'>y</span> <span class='hs-varid'>pf</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>liquidAssert</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>y</span><span class='hs-layout'>)</span> <span class='hs-num'>10</span>
</pre>

as the corresponding SMT query
<pre><span class=hs-linenum>87: </span>    <span class='hs-layout'>(</span><span class='hs-varid'>pf</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>_</span><span class='hs-keyglyph'>|</span><span class='hs-keyword'>_</span> <span class='hs-varop'>||</span> <span class='hs-varid'>x</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>y</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>y</span><span class='hs-layout'>)</span>
</pre>

is, thanks to the pesky `_|_`, not valid. 

Terminating The Bottom
----------------------

Thus, to make LiquidHaskell tell the truth while also not just pessimistically 
rejecting perfectly good programs, we need a way to get rid of the `_|_`. That 
is, we require a means of teaching LiquidHaskell to determine when a value
is *definitely* not bottom. 

In other words, we need to teach LiquidHaskell how to prove that a computation 
definitely terminates.

[ref-lies]:  /blog/2013/11/23/telling_lies.lhs/ 
