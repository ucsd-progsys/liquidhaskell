---
layout: post
title: Checking Termination
date: 2013-12-09 16:12
comments: true
tags: termination
author: Niki Vazou
published: true 
demo: Termination.hs
---

As explained in the [last][ref-lies] [two][ref-bottom] posts, we need a termination
checker to ensure that LiquidHaskell is not tricked by divergent, lazy
computations into telling lies. Happily, it turns out that with very 
little retrofitting, and a bit of jiu jitsu, we can use refinements 
themselves to prove termination!

<!-- more -->

<br>

<div class="row-fluid">
   <div class="span12 pagination-centered">
   <p style="text-align:center">
   <img class="center-block" src="/static/img/falling.jpg" alt="Falling Down" width="300">
       <br>
       How do you prove this fellow will stop falling?
       <br>
   </p>
   </div>
</div>




<pre><span class=hs-linenum>38: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Termination</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>39: </span>
<span class=hs-linenum>40: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span>     <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>sum</span><span class='hs-layout'>)</span>
<span class=hs-linenum>41: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Vector</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>sum</span><span class='hs-layout'>)</span>
</pre>

Lets first see how LiquidHaskell proves termination on simple 
recursive functions, and then later, we'll see how to look at 
fancier cases.

Looping Over Vectors
--------------------

Lets write a bunch of little functions that operate on 1-dimensional vectors


<pre><span class=hs-linenum>54: </span><span class='hs-keyword'>type</span> <span class='hs-conid'>Val</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>55: </span><span class='hs-keyword'>type</span> <span class='hs-conid'>Vec</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Vector</span> <span class='hs-conid'>Val</span>
</pre>

Next, lets write a simple recursive function that loops over to add up
the first `n` elements of a vector:


<pre><span class=hs-linenum>62: </span><span class='hs-definition'>sum</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Vec</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Val</span>
<span class=hs-linenum>63: </span><a class=annot href="#"><span class=annottext>x1:(Data.Vector.Vector (GHC.Types.Int))
-&gt; {VV : (GHC.Types.Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; (vlen x1))}
-&gt; (GHC.Types.Int)</span><span class='hs-definition'>sum</span></a> <a class=annot href="#"><span class=annottext>(Data.Vector.Vector (GHC.Types.Int))</span><span class='hs-varid'>a</span></a> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(GHC.Prim.Int#) -&gt; {VV : (GHC.Types.Int) | (VV == (x1  :  int))}</span><span class='hs-num'>0</span></a>
<span class=hs-linenum>64: </span><span class='hs-definition'>sum</span> <span class='hs-varid'>a</span> <span class='hs-varid'>n</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Data.Vector.Vector (GHC.Types.Int)) | (VV == a) &amp;&amp; ((vlen VV) &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x1:(Data.Vector.Vector (GHC.Types.Int))
-&gt; {VV : (GHC.Types.Int) | (VV &lt; (vlen x1)) &amp;&amp; (0 &lt;= VV)}
-&gt; (GHC.Types.Int)</span><span class='hs-varop'>!</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; (vlen a))}</span><span class='hs-varid'>n</span></a><a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV == (x1 - x2))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV == (x1 + x2))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>x1:(Data.Vector.Vector (GHC.Types.Int))
-&gt; {VV : (GHC.Types.Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; (vlen x1))}
-&gt; (GHC.Types.Int)</span><span class='hs-varid'>sum</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Vector.Vector (GHC.Types.Int)) | (VV == a) &amp;&amp; ((vlen VV) &gt;= 0)}</span><span class='hs-varid'>a</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; (vlen a))}</span><span class='hs-varid'>n</span></a><a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV == (x1 - x2))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span>
</pre>

Proving Termination By Hand(waving) 
-----------------------------------

Does `sum` terminate? 

First off, it is apparent that if we call `sum` with a
negative `n` then it **will not** terminate. 
Thus, we should only call `sum` with non-negative integers.

Fine, lets assume `n` is non-negative. Why then does it terminate?

Intuitively,

1. If `n` is `0` then it trivially returns with the value `0`.

2. If `n` is non-zero, then we recurse *but* with a strictly smaller `n` ...

3. ... but ultimately hit `0` at which point it terminates.

Thus we can, somewhat more formally, prove termination by induction on `n`. 

**Base Case** `n == 0` The function clearly terminates for the base case input of `0`.

**Inductive Hypothesis** Lets assume that `sum` terminates on all `0 <= k < n`.

**Inductive Step** Prove that `sum n` only recursively invokes `sum` with values that
satisfy the inductive hypothesis and hence, which terminate.

This reasoning suffices to convince ourselves that `sum i` terminates for 
every natural number `i`. That is, we have shown that `sum` terminates 
because a *well-founded metric* (i.e., the natural number `i`) is decreasing 
at each recursive call.

Proving Termination By Types
----------------------------

We can teach LiquidHaskell to prove termination by applying the same reasoning 
as above, by rephrasing it in terms of refinement types.

First, we specify that the input is restricted to the set of `Nat`ural numbers


<pre><span class=hs-linenum>109: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>sum</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-conop'>:</span><span class='hs-conid'>Vec</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| v &lt; (vlen a)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Val</span> <span class='hs-keyword'>@-}</span>
</pre>

where recall that `Nat` is just the refinement type `{v:Int | v >= 0}`.

Second, we typecheck the *body* of `sum` under an environment that
restricts `sum` to only be called on inputs less than `n`, i.e. using
an environment:

-  `a   :: Vec`
-  `n   :: Nat`
-  `sum :: Vec -> n':{v:Nat | v < n} -> Val`

This ensures that any (recursive) call in the body only calls `sum` 
with inputs smaller than the current parameter `n`. Since its body 
typechecks in this environment, i.e. `sum` is called with `n-1` which 
is smaller than `n` and, in this case, a `Nat`, LiquidHaskell proves 
that sum terminates for all `n`.

For those keeping track at home, this is the technique of 
[sized types](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.124.5589), 
, expressed using refinements. Sized types themselves are an instance of 
the classical method of proving termination via well founded metrics that 
goes back, at least, to [Turing](http://www.turingarchive.org/viewer/?id=462&title=01b).

Choosing the Correct Argument
-----------------------------

The example above is quite straightforward, and you might well wonder if this
method works well for ``real-world" programs. With a few generalizations
and extensions, and by judiciously using the wealth of information captured in
refinement types, the answer is an emphatic, yes!

Lets see one extension today.

We saw that liquidHaskell can happily check that some Natural number is decreasing
at each iteration, but it uses a na&#239;ve heuristic to choose which one -- for
now, assume that it always chooses *the first* `Int` parameter.

As you might imagine, this is quite simpleminded. 

Consider, a tail-recursive implementation of `sum`:


<pre><span class=hs-linenum>153: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>sum'</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-conop'>:</span><span class='hs-conid'>Vec</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Val</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span><span class='hs-keyword'>| v &lt; (vlen a)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Val</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>154: </span><span class='hs-definition'>sum'</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Vec</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Val</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Val</span>
<span class=hs-linenum>155: </span><a class=annot href="#"><span class=annottext>x1:(Data.Vector.Vector (GHC.Types.Int))
-&gt; (GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; (vlen x1))}
-&gt; (GHC.Types.Int)</span><span class='hs-definition'>sum'</span></a> <a class=annot href="#"><span class=annottext>(Data.Vector.Vector (GHC.Types.Int))</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>acc</span></a> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == acc)}</span><span class='hs-varid'>acc</span></a> <a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV == (x1 + x2))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Vector.Vector (GHC.Types.Int)) | (VV == a) &amp;&amp; ((vlen VV) &gt;= 0)}</span><span class='hs-varid'>a</span></a><a class=annot href="#"><span class=annottext>x1:(Data.Vector.Vector (GHC.Types.Int))
-&gt; {VV : (GHC.Types.Int) | (VV &lt; (vlen x1)) &amp;&amp; (0 &lt;= VV)}
-&gt; (GHC.Types.Int)</span><span class='hs-varop'>!</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (0  :  int))}</span><span class='hs-num'>0</span></a> 
<span class=hs-linenum>156: </span><span class='hs-definition'>sum'</span> <span class='hs-varid'>a</span> <span class='hs-varid'>acc</span> <span class='hs-varid'>n</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(Data.Vector.Vector (GHC.Types.Int))
-&gt; (GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; (vlen x1))}
-&gt; (GHC.Types.Int)</span><span class='hs-varid'>sum'</span></a> <a class=annot href="#"><span class=annottext>{VV : (Data.Vector.Vector (GHC.Types.Int)) | (VV == a) &amp;&amp; ((vlen VV) &gt;= 0)}</span><span class='hs-varid'>a</span></a> <span class='hs-layout'>(</span><span class=hs-error><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == acc)}</span><span class='hs-varid'>acc</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV == (x1 + x2))}</span><span class='hs-varop'>+</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{VV : (Data.Vector.Vector (GHC.Types.Int)) | (VV == a) &amp;&amp; ((vlen VV) &gt;= 0)}</span><span class='hs-varid'>a</span></a></span><span class=hs-error><a class=annot href="#"><span class=annottext>x1:(Data.Vector.Vector (GHC.Types.Int))
-&gt; {VV : (GHC.Types.Int) | (VV &lt; (vlen x1)) &amp;&amp; (0 &lt;= VV)}
-&gt; (GHC.Types.Int)</span><span class='hs-varop'>!</span></a></span><span class=hs-error><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; (vlen a))}</span><span class='hs-varid'>n</span></a></span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; (vlen a))}</span><span class='hs-varid'>n</span></a><a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV == (x1 - x2))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span>
</pre>

Clearly, the proof fails as liquidHaskell wants to prove that the `acc`umulator 
is a `Nat`ural number that decreases at each iteration, neither of which may be
true.

The remedy is easy. We can point liquidHaskell to the correct argument `n` using a `Decrease` annotation: 
<pre><span class=hs-linenum>164: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>Decrease</span> <span class='hs-varid'>sum'</span> <span class='hs-num'>3</span> <span class='hs-keyword'>@-}</span>
</pre>
which directs liquidHaskell to verify that the *third* argument (i.e., `n`) is decreasing. 
With this hint, liquidHaskell will happily verify that `sum'` is indeed a terminating function.

Thats all for now, next time we'll see how the basic technique can be extended
to a variety of real-world settings.

[ref-lies]:  /blog/2013/11/23/telling-lies.lhs/ 
[ref-bottom]: /blog/2013/12/01/getting-to-the-bottom.lhs/
