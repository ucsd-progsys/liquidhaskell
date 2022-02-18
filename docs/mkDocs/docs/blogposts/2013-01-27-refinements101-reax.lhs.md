---
layout: post
title: Refinements 101 (contd.) 
date: 2013-01-27 16:12
author: Ranjit Jhala
published: true 
comments: true
tags:
   - basic
demo: refinements101reax.hs
---

Hopefully, the [previous][ref101] article gave you a basic idea about what
refinement types look like. Several folks had interesting questions, that
are worth discussing in a separate post, since they throw a lot of light 
on the strengths (or weaknesses, depending on your point of view!) of
LiquidHaskell.

<!-- more -->


<pre><span class=hs-linenum>22: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Refinements101Reax</span> <span class='hs-keyword'>where</span>
</pre>

How to relate outputs and inputs 
--------------------------------

Recall the function `divide`


<pre><span class=hs-linenum>31: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>divide</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| v /= 0 }</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>32: </span><span class='hs-definition'>divide</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>33: </span><a class=annot href="#"><span class=annottext>(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV != 0)} -&gt; (GHC.Types.Int)</span><span class='hs-definition'>divide</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[(GHC.Types.Char)] -&gt; {VV : (GHC.Types.Int) | false}</span><span class='hs-varid'>error</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"divide by zero"</span></a>
<span class=hs-linenum>34: </span><span class='hs-definition'>divide</span> <span class='hs-varid'>n</span> <span class='hs-varid'>d</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = n)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x / y))}</span><span class='hs-varop'>`div`</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV != 0)}</span><span class='hs-varid'>d</span></a>
</pre>

and `abz` was the absolute value function


<pre><span class=hs-linenum>40: </span><span class='hs-definition'>abz</span>               <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>41: </span><a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | ((VV = 0) &lt;=&gt; (x = 0)),(0 &lt;= VV)}</span><span class='hs-definition'>abz</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a> <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt; y))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = n)}</span><span class='hs-varid'>n</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = n)}</span><span class='hs-varid'>n</span></a>
<span class=hs-linenum>42: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x - y))}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = n)}</span><span class='hs-varid'>n</span></a>
</pre>

[nanothief](http://www.reddit.com/user/nanothief) [remarked][qreddit101]
that LiquidHaskell was unable to verify the safety of the following call to
`divide` (i.e. was unable to show that `x` was non-zero at the callsite).


<pre><span class=hs-linenum>50: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>f</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>51: </span><a class=annot href="#"><span class=annottext>(GHC.Types.Int) -&gt; (GHC.Types.Int)</span><span class='hs-definition'>f</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | ((VV = 0) &lt;=&gt; (x = 0)),(0 &lt;= VV)}</span><span class='hs-varid'>abz</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (GHC.Types.Int) | (VV &gt;= 0),(0 &lt;= VV)}
-&gt; y:{VV : (GHC.Types.Int) | (VV &gt;= 0),(0 &lt;= VV)}
-&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x = y))}</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(GHC.Prim.Int#) -&gt; {VV : (GHC.Types.Int) | (VV = (x  :  int))}</span><span class='hs-num'>3</span></a>
<span class=hs-linenum>52: </span>    <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (3  :  int))}</span><span class='hs-num'>3</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV != 0)} -&gt; (GHC.Types.Int)</span><span class='hs-varop'>`divide`</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = x)}</span><span class='hs-varid'>x</span></a>
</pre>

Nanothief correctly argues that the code is clearly safe as *"`abz x == 0` being false implies `x /= 0`"*. 
Indeed, the code *is safe*, however, the reason that LiquidHaskell
rejected it has nothing to do with its inability
to  *"track the constraints of values based on tests using new values derived from that value"* as Nanothief surmised,
but instead, because LiquidHaskell supports **modular verification** 
where the *only* thing known about `abz` at a *use site* is 
whatever is specified in its *type*. 

Concretely speaking, the type 
<pre><span class=hs-linenum>64: </span><span class='hs-definition'>abz</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-num'>0</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span> <span class='hs-layout'>}</span>
</pre>

is too anemic to verify `f` above, as it tells us nothing 
about the *relationship* between the output and input -- looking at it,
we have now way of telling that when the *output* (of `abz`) is 
non-zero, the *input*  must also have been non-zero.

Instead, we can write a *stronger* type which does capture this information, for example
<pre><span class=hs-linenum>73: </span><span class='hs-definition'>abz</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-keyword'>if</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-varop'>&gt;</span> <span class='hs-num'>0</span><span class='hs-layout'>)</span> <span class='hs-keyword'>then</span> <span class='hs-varid'>x</span> <span class='hs-keyword'>else</span> <span class='hs-layout'>(</span><span class='hs-num'>0</span> <span class='hs-comment'>-</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>

 where 
<pre><span class=hs-linenum>77: </span><span class='hs-definition'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-keyword'>if</span> <span class='hs-varid'>p</span> <span class='hs-keyword'>then</span> <span class='hs-varid'>e1</span> <span class='hs-keyword'>else</span> <span class='hs-varid'>e2</span><span class='hs-layout'>)</span>
</pre>

 is an abbreviation for the formula 
<pre><span class=hs-linenum>81: </span><span class='hs-layout'>(</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>v</span> <span class='hs-varop'>==</span> <span class='hs-varid'>e1</span><span class='hs-layout'>)</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varid'>not</span> <span class='hs-varid'>p</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>e2</span><span class='hs-layout'>)</span>
</pre>

With this specification for `abz`, LiquidHaskell is able to reason that
when `abz x` is non-zero, `x` is also non-zero. Of course, `abz` is trivial 
enough that we can very precisely capture its *exact* semantics in the 
refinement type, but thats is rarely the case. 

Nevertheless, even here, you could write a somewhat *weaker* specification,
that still had enough juice to allow the verification of the `divide` call
in `f`. In particular, we might write


<pre><span class=hs-linenum>94: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>abz</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| ((0 &lt;= v) &amp;&amp; ((v = 0) &lt;=&gt; (x = 0))) }</span> <span class='hs-keyword'>@-}</span>
</pre>

which states the output is `0` *if and only if* the input is `0`.
LiquidHaskell will happily verify that `abz` implements this specification,
and will use it to verify the safety of `f` above.

(BTW, follow the link above to *demo this code*  yourself.)

How to tell a Fib
-----------------

[Chris Done](https://twitter.com/christopherdone) [asked][qblog101]
why LiquidHaskell refused to verify the following definition of `fib`.


<pre><span class=hs-linenum>110: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fib</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{ b:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| (n &gt;= 0 &amp;&amp; b &gt;= n) }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>111: </span><span class='hs-definition'>fib</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>112: </span><span class=hs-error><a class=annot href="#"><span class=annottext>n:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV &gt;= n),(n &gt;= 0)}</span><span class='hs-definition'>fib</span></a></span> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(GHC.Prim.Int#) -&gt; {VV : (GHC.Types.Int) | (VV = (x  :  int))}</span><span class='hs-num'>0</span></a>
<span class=hs-linenum>113: </span><span class='hs-definition'>fib</span> <span class='hs-num'>1</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(GHC.Prim.Int#) -&gt; {VV : (GHC.Types.Int) | (VV = (x  :  int))}</span><span class='hs-num'>1</span></a>
<span class=hs-linenum>114: </span><span class='hs-definition'>fib</span> <span class='hs-varid'>n</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>n:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV &gt;= n),(n &gt;= 0)}</span><span class='hs-varid'>fib</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a><a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x - y))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>n:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV &gt;= n),(n &gt;= 0)}</span><span class='hs-varid'>fib</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a><a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x - y))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (2  :  int))}</span><span class='hs-num'>2</span></a><span class='hs-layout'>)</span>
</pre>

Indeed, the both the *specification* and the *implementation* look pretty
legit, so what gives?  It turns out that there are *two* different reasons why. 

**Reason 1: Assumptions vs. Guarantees**

What we really want to say over here is that the *input* `n` 
is non-negative. However, putting the refinement `n >= 0` in 
the *output* constraint means that it becomes something that 
LiquidHaskell checks that the function `fib` **guarantees** 
(or **ensures**).
That is, the type states that we can pass `fib` *any* value 
`n` (including *negative* values) and yet, `fib` must return 
values `b` such that `b >= n` *and* `n >= 0`. 

The latter requirement is a rather tall order when an arbitrary `n` 
is passed in as input. `fib` can make no such guarantees since 
it was *given* the value `n` as a parameter. The only way `n` could 
be non-negative was that if the caller had sent in a non-negative value. 
Thus, we want to put the *burden of proof* on the right entity here, 
namely the caller.

To assign the burden of proof appropriately, we place the
non-negative refinement on the *input type*


<pre><span class=hs-linenum>142: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fib'</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v &gt;= 0}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{b:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| (n &gt;= 0 &amp;&amp; b &gt;= n) }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>143: </span><span class='hs-definition'>fib'</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>144: </span><span class=hs-error><a class=annot href="#"><span class=annottext>n:{VV : (GHC.Types.Int) | (VV &gt;= 0)}
-&gt; {VV : (GHC.Types.Int) | (VV &gt;= n),(n &gt;= 0)}</span><span class='hs-definition'>fib'</span></a></span> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(GHC.Prim.Int#) -&gt; {VV : (GHC.Types.Int) | (VV = (x  :  int))}</span><span class='hs-num'>0</span></a>
<span class=hs-linenum>145: </span><span class='hs-definition'>fib'</span> <span class='hs-num'>1</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(GHC.Prim.Int#) -&gt; {VV : (GHC.Types.Int) | (VV = (x  :  int))}</span><span class='hs-num'>1</span></a>
<span class=hs-linenum>146: </span><span class='hs-definition'>fib'</span> <span class='hs-varid'>n</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>n:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV &gt;= n),(n &gt;= 0)}</span><span class='hs-varid'>fib</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt;= 0)}</span><span class='hs-varid'>n</span></a><a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x - y))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>n:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV &gt;= n),(n &gt;= 0)}</span><span class='hs-varid'>fib</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt;= 0)}</span><span class='hs-varid'>n</span></a><a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x - y))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (2  :  int))}</span><span class='hs-num'>2</span></a><span class='hs-layout'>)</span>
</pre>

where now at *calls to* `fib'` LiquidHaskell will check that the argument
is non-negative, and furthermore, when checking `fib'` LiquidHaskell will 
**assume** that the parameter `n` is indeed non-negative. So now the
constraint `n >= 0` on the output is somewhat redundant, and the
non-negative `n` guarantee holds trivially.

**Reason 2: The Specification is a Fib**

If you run the above in the demo, you will see that LiquidHaskell still
doth protest loudly, and frankly, one might start getting a little
frustrated at the stubbornness and petulance of the checker.

 However, if you stare at the implementation, you will see that it in fact, *does not* meet the specification, as
<pre><span class=hs-linenum>162: </span><span class='hs-definition'>fib'</span> <span class='hs-num'>2</span>  <span class='hs-varop'>==</span> <span class='hs-varid'>fib'</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-varid'>fib'</span> <span class='hs-num'>0</span>
<span class=hs-linenum>163: </span>        <span class='hs-varop'>==</span> <span class='hs-num'>0</span> <span class='hs-varop'>+</span> <span class='hs-num'>1</span>
<span class=hs-linenum>164: </span>        <span class='hs-varop'>==</span> <span class='hs-num'>1</span>
</pre>

LiquidHaskell is reluctant to prove things that are false. Rather than 
anthropomorphize frivolously, lets see why it is unhappy. 

First, recall the somewhat simplified specification 
<pre><span class=hs-linenum>171: </span><span class='hs-definition'>fib'</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span> <span class='hs-varid'>b</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>b</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span> <span class='hs-layout'>}</span> 
</pre>

As we saw in the discussion about `abz`, at each recursive callsite
the *only information* LiquidHaskell uses about the returned value, 
is that described in the *output type* for that function call.

Thus, LiquidHaskell reasons that the expression:
<pre><span class=hs-linenum>179: </span><span class='hs-definition'>fib'</span> <span class='hs-layout'>(</span><span class='hs-varid'>n</span><span class='hs-comment'>-</span><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varop'>+</span> <span class='hs-varid'>fib'</span> <span class='hs-layout'>(</span><span class='hs-varid'>n</span><span class='hs-comment'>-</span><span class='hs-num'>2</span><span class='hs-layout'>)</span>
</pre>

has the type
<pre><span class=hs-linenum>183: </span><span class='hs-layout'>{</span><span class='hs-varid'>b</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>exists</span> <span class='hs-varid'>b1</span><span class='hs-layout'>,</span> <span class='hs-varid'>b2</span><span class='hs-varop'>.</span> <span class='hs-varid'>b</span>  <span class='hs-varop'>==</span> <span class='hs-varid'>b1</span> <span class='hs-varop'>+</span> <span class='hs-varid'>b2</span> 
<span class=hs-linenum>184: </span>                      <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>b1</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>n</span><span class='hs-comment'>-</span><span class='hs-num'>1</span> 
<span class=hs-linenum>185: </span>                      <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>b2</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>n</span><span class='hs-comment'>-</span><span class='hs-num'>2</span>     <span class='hs-layout'>}</span>
</pre>

where the `b1` and `b2` denote the values returned by the 
recursive calls --- we get the above by plugging the parameters
`n-1` and `n-2` in for the parameter `n` in output type for `fib'`.

The SMT solver simplifies the above to
<pre><span class=hs-linenum>193: </span><span class='hs-layout'>{</span><span class='hs-varid'>b</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>b</span> <span class='hs-varop'>&gt;=</span> <span class='hs-num'>2</span><span class='hs-varid'>n</span> <span class='hs-comment'>-</span> <span class='hs-num'>3</span><span class='hs-layout'>}</span>
</pre>

 Finally, to check the output guarantee is met, LiquidHaskell asks the SMT solver to prove that
<pre><span class=hs-linenum>197: </span><span class='hs-layout'>(</span><span class='hs-varid'>b</span> <span class='hs-varop'>&gt;=</span> <span class='hs-num'>2</span><span class='hs-varid'>n</span> <span class='hs-comment'>-</span> <span class='hs-num'>2</span><span class='hs-layout'>)</span>  <span class='hs-keyglyph'>=&gt;</span>  <span class='hs-layout'>(</span><span class='hs-varid'>b</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span>
</pre>

The SMT solver will refuse, of course, since the above implication is 
*not valid* (e.g. when `n` is `2`) Thus, via SMT, LiquidHaskell proclaims
that the function `fib'` does not implement the advertised type and hence
marks it *unsafe*.

Fixing The Code
---------------

How then, do we get Chris' specification to work out? It seems like it 
*should* hold (except for that pesky case where `n=2`. Indeed,
let's rig the code, so that all the base cases return `1`.


<pre><span class=hs-linenum>213: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fibOK</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{b:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| ((b &gt;= n) &amp;&amp; (b &gt;= 1))}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>214: </span><span class='hs-definition'>fibOK</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>215: </span><a class=annot href="#"><span class=annottext>n:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV &gt;= 1),(VV &gt;= n)}</span><span class='hs-definition'>fibOK</span></a> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(GHC.Prim.Int#) -&gt; {VV : (GHC.Types.Int) | (VV = (x  :  int))}</span><span class='hs-num'>1</span></a>
<span class=hs-linenum>216: </span><span class='hs-definition'>fibOK</span> <span class='hs-num'>1</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(GHC.Prim.Int#) -&gt; {VV : (GHC.Types.Int) | (VV = (x  :  int))}</span><span class='hs-num'>1</span></a>
<span class=hs-linenum>217: </span><span class='hs-definition'>fibOK</span> <span class='hs-varid'>n</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>n:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV &gt;= 1),(VV &gt;= n)}</span><span class='hs-varid'>fibOK</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a><a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x - y))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>n:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV &gt;= 1),(VV &gt;= n)}</span><span class='hs-varid'>fibOK</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a><a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x - y))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (2  :  int))}</span><span class='hs-num'>2</span></a><span class='hs-layout'>)</span>
</pre>

Here' we specify that not only is the output greater than the input, it is
**also** greater than `1`. 

 Now in the recursive case, LiquidHaskell reasons that the value being output is
<pre><span class=hs-linenum>224: </span><span class='hs-layout'>{</span><span class='hs-varid'>b</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>exists</span> <span class='hs-varid'>b1</span><span class='hs-layout'>,</span> <span class='hs-varid'>b2</span><span class='hs-varop'>.</span> <span class='hs-varid'>b</span>  <span class='hs-varop'>==</span> <span class='hs-varid'>b1</span> <span class='hs-varop'>+</span> <span class='hs-varid'>b2</span> 
<span class=hs-linenum>225: </span>                      <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>b1</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>n</span><span class='hs-comment'>-</span><span class='hs-num'>1</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>b1</span> <span class='hs-varop'>&gt;=</span> <span class='hs-num'>1</span> 
<span class=hs-linenum>226: </span>                      <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>b2</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>n</span><span class='hs-comment'>-</span><span class='hs-num'>2</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>b2</span> <span class='hs-varop'>&gt;=</span> <span class='hs-num'>1</span> <span class='hs-layout'>}</span>
</pre>

which reduces to 
<pre><span class=hs-linenum>230: </span><span class='hs-layout'>{</span><span class='hs-varid'>b</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>2</span><span class='hs-varid'>n</span> <span class='hs-comment'>-</span> <span class='hs-num'>3</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>n</span> <span class='hs-varop'>&gt;=</span> <span class='hs-num'>2</span> <span class='hs-layout'>}</span>
</pre>

which, the SMT solver is happy to verify, is indeed a subtype
<pre><span class=hs-linenum>234: </span><span class='hs-keyword'>of</span> <span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-varop'>.</span><span class='hs-varid'>e</span><span class='hs-varop'>.</span> <span class='hs-varid'>implies</span> <span class='hs-varid'>the</span> <span class='hs-varid'>refinement</span> <span class='hs-keyword'>of</span><span class='hs-layout'>)</span> <span class='hs-varid'>the</span> <span class='hs-varid'>specified</span> <span class='hs-varid'>output</span>
<span class=hs-linenum>235: </span><span class='hs-layout'>{</span><span class='hs-varid'>b</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>b</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>n</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>b</span> <span class='hs-varop'>&gt;=</span> <span class='hs-num'>1</span> <span class='hs-layout'>}</span> 
</pre>

Conclusion
----------

There are several things to take away. 

1. We need to distinguish between *assumptions* and *guarantees* 
   when writing specifications for functions.

2. For *modularity*, LiquidHaskell, like every type system, uses only
   the (refinement) *type*  of each function at each use site, and not the 
   function's *body*.

3. Some seemingly intuitive specifications often aren't; in future work it
   would be useful to actually [generate][mlton]  [tests][concolic] as 
   [counterexamples][icse04] that illustrate when a specification
   [fails][dsd].

[qblog101]: /blog/2013/01/01/refinement-types-101.lhs/#comment-772807850
[qreddit101]: http://www.reddit.com/r/haskell/comments/16w3hp/liquidhaskell_refinement_types_in_haskell_via_smt/c809160
[ref101]:  /blog/2013/01/01/refinement-types-101.lhs/ 
[concolic]: http://en.wikipedia.org/wiki/Concolic_testing
[icse04]: http://goto.ucsd.edu/~rjhala/papers/generating_tests_from_counterexamples.html
[dsd]: http://dl.acm.org/citation.cfm?doid=1348250.1348254
[mlton]: http://www.cs.purdue.edu/homes/zhu103/pubs/vmcai13.pdf

