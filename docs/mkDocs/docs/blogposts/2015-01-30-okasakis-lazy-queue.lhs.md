---
layout: post
title: Okasaki's Lazy Queues
date: 2015-01-28
comments: true
author: Ranjit Jhala 
published: true
tags:
   - measures
demo: LazyQueue.hs
---

The "Hello World!" example for fancy type systems is probably the sized vector
or list `append` function ("The output has size equal to the *sum* of the
inputs!").  One the one hand, it is perfect: simple enough to explain without
pages of code, yet complex enough to show off whats cool about dependency. On
the other hand, like the sweater I'm sporting right now, it's a bit well-worn and
worse, was never wholly convincing ("Why do I *care* what the *size* of the
output list is anyway?")

Recently, I came across a nice example that is almost as simple, but is also
well motivated: Okasaki's beautiful [Lazy Amortized Queues][okasaki95].  This
structure leans heavily on an invariant to provide fast *insertion* and
*deletion*. Let's see how to enforce that invariant with LiquidHaskell.

<!-- more -->

<div class="hidden">

<pre><span class=hs-linenum>30: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-termination"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>31: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--total"</span>          <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>32: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--maxparams=3"</span>    <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>33: </span>
<span class=hs-linenum>34: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>LazyQueue</span> <span class='hs-layout'>(</span><span class='hs-conid'>Queue</span><span class='hs-layout'>,</span> <span class='hs-varid'>insert</span><span class='hs-layout'>,</span> <span class='hs-varid'>remove</span><span class='hs-layout'>,</span> <span class='hs-varid'>emp</span><span class='hs-layout'>)</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>35: </span>
<span class=hs-linenum>36: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>length</span><span class='hs-layout'>)</span>
<span class=hs-linenum>37: </span>
<span class=hs-linenum>38: </span><span class='hs-comment'>-- | Size function actually returns the size: (Duh!)</span>
<span class=hs-linenum>39: </span>
<span class=hs-linenum>40: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>size</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>q</span><span class='hs-conop'>:</span><span class='hs-conid'>SList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| v = size q}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>41: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>Queue</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Q</span>  <span class='hs-layout'>{</span> <a class=annot href="#"><span class=annottext>forall a. (LazyQueue.Queue a) -&gt; (LazyQueue.SList a)</span><span class='hs-varid'>front</span></a> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>SList</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>42: </span>                  <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>forall a. (LazyQueue.Queue a) -&gt; (LazyQueue.SList a)</span><span class='hs-varid'>back</span></a>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>SList</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>43: </span>                  <span class='hs-layout'>}</span>
<span class=hs-linenum>44: </span>
<span class=hs-linenum>45: </span><span class='hs-comment'>-- Source: Okasaki, JFP 1995</span>
<span class=hs-linenum>46: </span><span class='hs-comment'>-- <a href="http://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/jfp95queue.pdf">http://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/jfp95queue.pdf</a></span>
<span class=hs-linenum>47: </span>
</pre>
</div>

Queues 
------

A [queue][queue-wiki] is a structure into which we can `insert` and `remove` data
such that the order in which the data is removed is the same as the order in which
it was inserted.

![A Queue](../static/img/queue.png)

To implement a queue *efficiently* one needs to have rapid access to both
the "head" as well as the "tail" because we `remove` elements from former
and `insert` elements into the latter. This is quite straightforward with
explicit pointers and mutation -- one uses an old school linked list and
maintains pointers to the head and the tail. But can we implement the
structure efficiently without having stoop so low?

Queues = Pair of Lists
----------------------

Almost two decades ago, Chris Okasaki came up with a very cunning way
to implement queues using a *pair* of lists -- let's call them `front`
and `back` which represent the corresponding parts of the Queue.

+ To `insert` elements, we just *cons* them onto the `back` list,
+ To `remove` elements, we just *un-cons* them from the `front` list.

![A Queue is Two Lists](../static/img/queue-lists.png)


The catch is that we need to shunt elements from the back to the
front every so often, e.g. when

1. a `remove` call is triggered, and
2. the `front` list is empty,

We can transfer the elements from the `back` to the `front`.


![Transferring Elements from Back to Front](../static/img/queue-rotate.png)

Okasaki observed that every element is only moved *once* from the
front to the back; hence, the time for `insert` and `lookup` could be
`O(1)` when *amortized* over all the operations. Awesome, right?!

Almost. Some set of unlucky `remove` calls (which occur when
the `front` is empty) are stuck paying the bill. They have a
rather high latency up to `O(n)` where `n` is the total number
of operations. Oops.

Queue = Balanced Lazy Lists
---------------------------

This is where Okasaki's beautiful insights kick in. Okasaki
observed that all we need to do is to enforce a simple invariant:

**Invariant:** Size of `front` >= Size of `back`

Now, if the lists are *lazy* i.e. only constructed as the head
value is demanded, then a single `remove` needs only a tiny `O(log n)`
in the worst case, and so no single `remove` is stuck paying the bill.

Let's see how to represent these Queues and ensure the crucial invariant(s)
with LiquidHaskell. What we need are the following ingredients:

1. A type for `List`s, and a way to track their `size`,

2. A type for `Queue`s which encodes the *balance* invariant -- ``front longer than back",

3. A way to implement the `insert`, `remove` and `transfer` operations.

Sized Lists
------------

The first part is super easy. Let's define a type:


<pre><span class=hs-linenum>127: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>SList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>SL</span> <span class='hs-layout'>{</span> <a class=annot href="#"><span class=annottext>forall a.
x1:(LazyQueue.SList a)
-&gt; {v : GHC.Types.Int | v == size x1 &amp;&amp; v &gt;= 0}</span><span class='hs-varid'>size</span></a> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>forall a. (LazyQueue.SList a) -&gt; [a]</span><span class='hs-varid'>elems</span></a> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-layout'>}</span>
</pre>

We have a special field that saves the `size` because otherwise, we
have a linear time computation that wrecks Okasaki's careful
analysis. (Actually, he presents a variant which does *not* require
saving the size as well, but that's for another day.)

But how can we be sure that `size` is indeed the *real size* of `elems`?

Let's write a function to *measure* the real size:


<pre><span class=hs-linenum>140: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>realSize</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>141: </span><span class='hs-definition'>realSize</span>      <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>142: </span><a class=annot href="#"><span class=annottext>forall a. x1:[a] -&gt; {VV : GHC.Types.Int | VV == realSize x1}</span><span class='hs-definition'>realSize</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:GHC.Prim.Int# -&gt; {v : GHC.Types.Int | v == (x1  :  int)}</span><span class='hs-num'>0</span></a>
<span class=hs-linenum>143: </span><span class='hs-definition'>realSize</span> <span class='hs-layout'>(</span><span class='hs-keyword'>_</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == (1  :  int)}</span><span class='hs-num'>1</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int
-&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>forall a. x1:[a] -&gt; {VV : GHC.Types.Int | VV == realSize x1}</span><span class='hs-varid'>realSize</span></a> <a class=annot href="#"><span class=annottext>{v : [a] | v == xs &amp;&amp; len v &gt;= 0}</span><span class='hs-varid'>xs</span></a>
</pre>

and now, we can simply specify a *refined* type for `SList` that ensures
that the *real* size is saved in the `size` field:


<pre><span class=hs-linenum>150: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>SList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>SL</span> <span class='hs-layout'>{</span>
<span class=hs-linenum>151: </span>       <span class='hs-varid'>size</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Nat</span> 
<span class=hs-linenum>152: </span>     <span class='hs-layout'>,</span> <span class='hs-varid'>elems</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>realSize</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>size</span><span class='hs-layout'>}</span>
<span class=hs-linenum>153: </span>     <span class='hs-layout'>}</span>
<span class=hs-linenum>154: </span>  <span class='hs-keyword'>@-}</span>
</pre>

As a sanity check, consider this:


<pre><span class=hs-linenum>160: </span><a class=annot href="#"><span class=annottext>{VV : (LazyQueue.SList {VV : [GHC.Types.Char] | len VV &gt;= 0}) | size VV &gt; 0}</span><span class='hs-definition'>okList</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0}
-&gt; x2:{v : [{v : [GHC.Types.Char] | len v &gt;= 0}] | realSize v == x1}
-&gt; {v : (LazyQueue.SList {v : [GHC.Types.Char] | len v &gt;= 0}) | elems v == x2 &amp;&amp; size v == x1}</span><span class='hs-conid'>SL</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == (1  :  int)}</span><span class='hs-num'>1</span></a> <a class=annot href="#"><span class=annottext>{v : [{v : [GHC.Types.Char] | len v &gt;= 0}]&lt;\_ VV -&gt; false&gt; | null v &lt;=&gt; false &amp;&amp; len v &gt;= 0}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{v : [GHC.Types.Char] | len v &gt;= 0}</span><span class='hs-str'>"cat"</span></a><span class='hs-keyglyph'>]</span>    <span class='hs-comment'>-- accepted</span>
<span class=hs-linenum>161: </span>
<span class=hs-linenum>162: </span><a class=annot href="#"><span class=annottext>forall a. (LazyQueue.SList a)</span><span class='hs-definition'>badList</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0}
-&gt; x2:{v : [a] | realSize v == x1}
-&gt; {v : (LazyQueue.SList a) | elems v == x2 &amp;&amp; size v == x1}</span><span class='hs-conid'>SL</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == (1  :  int)}</span><span class='hs-num'>1</span></a> <span class=hs-error><a class=annot href="#"><span class=annottext>{v : [a] | null v &lt;=&gt; true &amp;&amp; realSize v == 0 &amp;&amp; len v == 0 &amp;&amp; len v &gt;= 0}</span><span class='hs-conid'>[]</span></a></span>         <span class='hs-comment'>-- rejected</span>
</pre>

It is helpful to define a few aliases for `SList`s of a size `N` and
non-empty `SList`s:


<pre><span class=hs-linenum>169: </span><span class='hs-comment'>-- | SList of size N</span>
<span class=hs-linenum>170: </span>
<span class=hs-linenum>171: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>SListN</span> <span class='hs-varid'>a</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>SList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>size</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>172: </span>
<span class=hs-linenum>173: </span><span class='hs-comment'>-- | Non-Empty SLists:</span>
<span class=hs-linenum>174: </span>
<span class=hs-linenum>175: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>NEList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>SList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>size</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&gt;</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>176: </span>
</pre>

Finally, we can define a basic API for `SList`.

**To Construct** lists, we use `nil` and `cons`:


<pre><span class=hs-linenum>184: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>nil</span>          <span class='hs-keyglyph'>::</span> <span class='hs-conid'>SListN</span> <span class='hs-varid'>a</span> <span class='hs-num'>0</span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>185: </span><a class=annot href="#"><span class=annottext>forall a. {v : (LazyQueue.SList a) | size v == 0}</span><span class='hs-definition'>nil</span></a>              <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0}
-&gt; x2:{v : [a] | realSize v == x1}
-&gt; {v : (LazyQueue.SList a) | elems v == x2 &amp;&amp; size v == x1}</span><span class='hs-conid'>SL</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == (0  :  int)}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>{v : [a] | null v &lt;=&gt; true &amp;&amp; realSize v == 0 &amp;&amp; len v == 0 &amp;&amp; len v &gt;= 0}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>186: </span>
<span class=hs-linenum>187: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>cons</span>         <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-conid'>SList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>SListN</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>{size xs + 1}</span>   <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>188: </span><a class=annot href="#"><span class=annottext>forall a.
a
-&gt; x2:(LazyQueue.SList a)
-&gt; {v : (LazyQueue.SList a) | size v == size x2 + 1}</span><span class='hs-definition'>cons</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>x</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>SL</span> <span class='hs-varid'>n</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0}
-&gt; x2:{v : [a] | realSize v == x1}
-&gt; {v : (LazyQueue.SList a) | elems v == x2 &amp;&amp; size v == x1}</span><span class='hs-conid'>SL</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == n &amp;&amp; v &gt;= 0}</span><span class='hs-varid'>n</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int
-&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a><a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == (1  :  int)}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | VV == x}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>x1:a
-&gt; x2:[a]
-&gt; {v : [a] | null v &lt;=&gt; false &amp;&amp; xListSelector v == x1 &amp;&amp; realSize v == 1 + realSize x2 &amp;&amp; xsListSelector v == x2 &amp;&amp; len v == 1 + len x2}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{v : [a] | v == xs &amp;&amp; realSize v == n &amp;&amp; len v &gt;= 0}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
</pre>

**To Destruct** lists, we have `hd` and `tl`.


<pre><span class=hs-linenum>194: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>tl</span>           <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-conid'>NEList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>SListN</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>{size xs - 1}</span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>195: </span><a class=annot href="#"><span class=annottext>forall a.
x1:{v : (LazyQueue.SList a) | size v &gt; 0}
-&gt; {v : (LazyQueue.SList a) | size v == size x1 - 1}</span><span class='hs-definition'>tl</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>SL</span> <span class='hs-varid'>n</span> <span class='hs-layout'>(</span><span class='hs-keyword'>_</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0}
-&gt; x2:{v : [a] | realSize v == x1}
-&gt; {v : (LazyQueue.SList a) | elems v == x2 &amp;&amp; size v == x1}</span><span class='hs-conid'>SL</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == n &amp;&amp; v &gt;= 0}</span><span class='hs-varid'>n</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int
-&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == (1  :  int)}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{v : [a] | v == xs &amp;&amp; len v &gt;= 0}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>196: </span>
<span class=hs-linenum>197: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>hd</span>           <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-conid'>NEList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>198: </span><a class=annot href="#"><span class=annottext>forall a. {v : (LazyQueue.SList a) | size v &gt; 0} -&gt; a</span><span class='hs-definition'>hd</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>SL</span> <span class='hs-keyword'>_</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | VV == x}</span><span class='hs-varid'>x</span></a> 
</pre>

Don't worry, they are perfectly *safe* as LiquidHaskell will make
sure we *only* call these operators on non-empty `SList`s. For example,


<pre><span class=hs-linenum>205: </span><a class=annot href="#"><span class=annottext>{v : [GHC.Types.Char] | len v &gt;= 0}</span><span class='hs-definition'>okHd</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList {v : [GHC.Types.Char] | len v &gt;= 0}) | size v &gt; 0}
-&gt; {v : [GHC.Types.Char] | len v &gt;= 0}</span><span class='hs-varid'>hd</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList {v : [GHC.Types.Char] | len v &gt;= 0}) | v == LazyQueue.okList &amp;&amp; size v &gt; 0}</span><span class='hs-varid'>okList</span></a>       <span class='hs-comment'>-- accepted</span>
<span class=hs-linenum>206: </span>
<span class=hs-linenum>207: </span><a class=annot href="#"><span class=annottext>{VV : [GHC.Types.Char] | len VV &gt;= 0}</span><span class='hs-definition'>badHd</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList {v : [GHC.Types.Char] | len v &gt;= 0}) | size v &gt; 0}
-&gt; {v : [GHC.Types.Char] | len v &gt;= 0}</span><span class='hs-varid'>hd</span></a> <span class='hs-layout'>(</span><span class=hs-error><a class=annot href="#"><span class=annottext>x1:{v : (LazyQueue.SList {v : [GHC.Types.Char] | len v &gt;= 0}) | size v &gt; 0}
-&gt; {v : (LazyQueue.SList {v : [GHC.Types.Char] | len v &gt;= 0}) | size v == size x1 - 1}</span><span class='hs-varid'>tl</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList {v : [GHC.Types.Char] | len v &gt;= 0}) | v == LazyQueue.okList &amp;&amp; size v &gt; 0}</span><span class='hs-varid'>okList</span></a></span><span class='hs-layout'>)</span>  <span class='hs-comment'>-- rejected</span>
</pre>


Queue Type
-----------

Now, it is quite straightforward to define the `Queue` type, as a pair of lists,
`front` and `back`, such that the latter is always smaller than the former:


<pre><span class=hs-linenum>218: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>Queue</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Q</span> <span class='hs-layout'>{</span>
<span class=hs-linenum>219: </span>       <span class='hs-varid'>front</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>SList</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>220: </span>     <span class='hs-layout'>,</span> <span class='hs-varid'>back</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>SListLE</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-varid'>size</span> <span class='hs-varid'>front</span><span class='hs-layout'>)</span>
<span class=hs-linenum>221: </span>     <span class='hs-layout'>}</span>
<span class=hs-linenum>222: </span>  <span class='hs-keyword'>@-}</span>
</pre>

Where the alias `SListLE a L` corresponds to lists with less than `N` elements:


<pre><span class=hs-linenum>228: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>SListLE</span> <span class='hs-varid'>a</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>SList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>size</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&lt;=</span> <span class='hs-conid'>N</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

As a quick check, notice that we *cannot represent illegal Queues*:


<pre><span class=hs-linenum>234: </span><a class=annot href="#"><span class=annottext>{VV : (LazyQueue.Queue [GHC.Types.Char]) | 0 &lt; qsize VV}</span><span class='hs-definition'>okQ</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(LazyQueue.SList [GHC.Types.Char])
-&gt; x2:{v : (LazyQueue.SList [GHC.Types.Char]) | size v &lt;= size x1}
-&gt; {v : (LazyQueue.Queue [GHC.Types.Char]) | qsize v == size x1 + size x2 &amp;&amp; front v == x1 &amp;&amp; back v == x2}</span><span class='hs-conid'>Q</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList {v : [GHC.Types.Char] | len v &gt;= 0}) | v == LazyQueue.okList &amp;&amp; size v &gt; 0}</span><span class='hs-varid'>okList</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList [GHC.Types.Char]) | size v == 0}</span><span class='hs-varid'>nil</span></a>  <span class='hs-comment'>-- accepted, |front| &gt; |back| </span>
<span class=hs-linenum>235: </span>
<span class=hs-linenum>236: </span><a class=annot href="#"><span class=annottext>{VV : (LazyQueue.Queue [GHC.Types.Char]) | 0 &lt; qsize VV}</span><span class='hs-definition'>badQ</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(LazyQueue.SList [GHC.Types.Char])
-&gt; x2:{v : (LazyQueue.SList [GHC.Types.Char]) | size v &lt;= size x1}
-&gt; {v : (LazyQueue.Queue [GHC.Types.Char]) | qsize v == size x1 + size x2 &amp;&amp; front v == x1 &amp;&amp; back v == x2}</span><span class='hs-conid'>Q</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList [GHC.Types.Char]) | size v == 0}</span><span class='hs-varid'>nil</span></a> <span class=hs-error><a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList {v : [GHC.Types.Char] | len v &gt;= 0}) | v == LazyQueue.okList &amp;&amp; size v &gt; 0}</span><span class='hs-varid'>okList</span></a></span>  <span class='hs-comment'>-- rejected, |front| &lt; |back|</span>
</pre>

**To Measure Queue Size** let us define a function


<pre><span class=hs-linenum>242: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>qsize</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>243: </span><span class='hs-definition'>qsize</span>         <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Queue</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>244: </span><a class=annot href="#"><span class=annottext>forall a.
x1:(LazyQueue.Queue a) -&gt; {VV : GHC.Types.Int | VV == qsize x1}</span><span class='hs-definition'>qsize</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Q</span> <span class='hs-varid'>l</span> <span class='hs-varid'>r</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(LazyQueue.SList a)
-&gt; {v : GHC.Types.Int | v == size x1 &amp;&amp; v &gt;= 0}</span><span class='hs-varid'>size</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == l}</span><span class='hs-varid'>l</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int
-&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>x1:(LazyQueue.SList a)
-&gt; {v : GHC.Types.Int | v == size x1 &amp;&amp; v &gt;= 0}</span><span class='hs-varid'>size</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == r &amp;&amp; size v &lt;= size l}</span><span class='hs-varid'>r</span></a>
</pre>

This will prove helpful to define `Queue`s of a given size `N` and
non-empty `Queue`s (from which values can be safely removed.)


<pre><span class=hs-linenum>251: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>QueueN</span> <span class='hs-varid'>a</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Queue</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>qsize</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>252: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>NEQueue</span> <span class='hs-varid'>a</span>  <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Queue</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-num'>0</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>qsize</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>


Queue Operations
----------------

Almost there! Now all that remains is to define the `Queue` API. The
code below is more or less identical to Okasaki's (I prefer `front`
and `back` to his `left` and `right`.)


**The Empty Queue** is simply one where both `front` and `back` are `nil`.


<pre><span class=hs-linenum>267: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>emp</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>QueueN</span> <span class='hs-varid'>a</span> <span class='hs-num'>0</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>268: </span><a class=annot href="#"><span class=annottext>forall a. {v : (LazyQueue.Queue a) | 0 == qsize v}</span><span class='hs-definition'>emp</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(LazyQueue.SList a)
-&gt; x2:{v : (LazyQueue.SList a) | size v &lt;= size x1}
-&gt; {v : (LazyQueue.Queue a) | qsize v == size x1 + size x2 &amp;&amp; front v == x1 &amp;&amp; back v == x2}</span><span class='hs-conid'>Q</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | size v == 0}</span><span class='hs-varid'>nil</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | size v == 0}</span><span class='hs-varid'>nil</span></a>
</pre>

**To Insert** an element we just `cons` it to the `back` list, and call
the *smart constructor* `makeq` to ensure that the balance invariant holds:


<pre><span class=hs-linenum>275: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>insert</span>       <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>q</span><span class='hs-conop'>:</span><span class='hs-conid'>Queue</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>QueueN</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>{qsize q + 1}</span>   <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>276: </span><a class=annot href="#"><span class=annottext>forall a.
a
-&gt; x2:(LazyQueue.Queue a)
-&gt; {v : (LazyQueue.Queue a) | qsize x2 + 1 == qsize v}</span><span class='hs-definition'>insert</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>e</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Q</span> <span class='hs-varid'>f</span> <span class='hs-varid'>b</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(LazyQueue.SList a)
-&gt; x2:{v : (LazyQueue.SList a) | size v &lt;= size x1 + 1}
-&gt; {v : (LazyQueue.Queue a) | size x1 + size v == qsize v}</span><span class='hs-varid'>makeq</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == f}</span><span class='hs-varid'>f</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | VV == e}</span><span class='hs-varid'>e</span></a> <a class=annot href="#"><span class=annottext>a
-&gt; x2:(LazyQueue.SList a)
-&gt; {v : (LazyQueue.SList a) | size v == size v + 1}</span><span class='hs-varop'>`cons`</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == b &amp;&amp; size v &lt;= size f}</span><span class='hs-varid'>b</span></a><span class='hs-layout'>)</span>
</pre>

**To Remove** an element we pop it off the `front` by using `hd` and `tl`.
Notice that the `remove` is only called on non-empty `Queue`s, which together
with the key balance invariant, ensures that the calls to `hd` and `tl` are safe.


<pre><span class=hs-linenum>284: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>remove</span>       <span class='hs-keyglyph'>::</span> <span class='hs-varid'>q</span><span class='hs-conop'>:</span><span class='hs-conid'>NEQueue</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span><span class='hs-layout'>,</span> <span class='hs-conid'>QueueN</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>{qsize q - 1}</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>285: </span><a class=annot href="#"><span class=annottext>forall a.
x1:{v : (LazyQueue.Queue a) | 0 &lt; qsize v}
-&gt; (a, {v : (LazyQueue.Queue a) | qsize x1 - 1 == qsize v})</span><span class='hs-definition'>remove</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Q</span> <span class='hs-varid'>f</span> <span class='hs-varid'>b</span><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a b -&gt; Prop&gt;.
x1:a
-&gt; x2:{VV : b&lt;p2 x1&gt; | true}
-&gt; {v : (a, b)&lt;\x6 VV -&gt; p2 x6&gt; | fst v == x1 &amp;&amp; x_Tuple22 v == x2 &amp;&amp; snd v == x2 &amp;&amp; x_Tuple21 v == x1}</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | size v &gt; 0} -&gt; a</span><span class='hs-varid'>hd</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == f}</span><span class='hs-varid'>f</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>x1:(LazyQueue.SList a)
-&gt; x2:{v : (LazyQueue.SList a) | size v &lt;= size x1 + 1}
-&gt; {v : (LazyQueue.Queue a) | size x1 + size v == qsize v}</span><span class='hs-varid'>makeq</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:{v : (LazyQueue.SList a) | size v &gt; 0}
-&gt; {v : (LazyQueue.SList a) | size v == size x1 - 1}</span><span class='hs-varid'>tl</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == f}</span><span class='hs-varid'>f</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == b &amp;&amp; size v &lt;= size f}</span><span class='hs-varid'>b</span></a><span class='hs-layout'>)</span>
</pre>

*Aside:* Why didn't we (or Okasaki) use a pattern match here?

**To Ensure the Invariant** we use the smart constructor `makeq`,
which is where the heavy lifting, such as it is, happens. The
constructor takes two lists, the front `f` and back `b` and if they
are balanced, directly returns the `Queue`, and otherwise transfers
the elements from `b` over using `rot`ate.


<pre><span class=hs-linenum>297: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>makeq</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>f</span><span class='hs-conop'>:</span><span class='hs-conid'>SList</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>298: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-conop'>:</span><span class='hs-conid'>SListLE</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>{size f + 1 }</span>
<span class=hs-linenum>299: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>QueueN</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>{size f + size b}</span>
<span class=hs-linenum>300: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>301: </span><a class=annot href="#"><span class=annottext>forall a.
x1:(LazyQueue.SList a)
-&gt; x2:{v : (LazyQueue.SList a) | size v &lt;= size x1 + 1}
-&gt; {v : (LazyQueue.Queue a) | size x1 + size x2 == qsize v}</span><span class='hs-definition'>makeq</span></a> <a class=annot href="#"><span class=annottext>(LazyQueue.SList a)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | size v &lt;= size f + 1}</span><span class='hs-varid'>b</span></a> 
<span class=hs-linenum>302: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>x1:(LazyQueue.SList a)
-&gt; {v : GHC.Types.Int | v == size x1 &amp;&amp; v &gt;= 0}</span><span class='hs-varid'>size</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == b &amp;&amp; size v &lt;= size f + 1}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int
-&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Bool | Prop v &lt;=&gt; x1 &lt;= v}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>x1:(LazyQueue.SList a)
-&gt; {v : GHC.Types.Int | v == size x1 &amp;&amp; v &gt;= 0}</span><span class='hs-varid'>size</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == f}</span><span class='hs-varid'>f</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(LazyQueue.SList a)
-&gt; x2:{v : (LazyQueue.SList a) | size v &lt;= size x1}
-&gt; {v : (LazyQueue.Queue a) | qsize v == size x1 + size x2 &amp;&amp; front v == x1 &amp;&amp; back v == x2}</span><span class='hs-conid'>Q</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == f}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == b &amp;&amp; size v &lt;= size f + 1}</span><span class='hs-varid'>b</span></a>
<span class=hs-linenum>303: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(LazyQueue.SList a)
-&gt; x2:{v : (LazyQueue.SList a) | size v &lt;= size x1}
-&gt; {v : (LazyQueue.Queue a) | qsize v == size x1 + size x2 &amp;&amp; front v == x1 &amp;&amp; back v == x2}</span><span class='hs-conid'>Q</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a.
x1:(LazyQueue.SList a)
-&gt; x2:{v : (LazyQueue.SList a) | size v == 1 + size x1}
-&gt; x3:(LazyQueue.SList a)
-&gt; {v : (LazyQueue.SList a) | size v == size x1 + size x2 + size x3}</span><span class='hs-varid'>rot</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == f}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == b &amp;&amp; size v &lt;= size f + 1}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | size v == 0}</span><span class='hs-varid'>nil</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | size v == 0}</span><span class='hs-varid'>nil</span></a>
</pre>

**The Rotate** function is only called when the `back` is one larger
than the `front` (we never let things drift beyond that). It is
arranged so that it the `hd` is built up fast, before the entire
computation finishes; which, combined with laziness provides the
efficient worst-case guarantee.


<pre><span class=hs-linenum>313: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>rot</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>f</span><span class='hs-conop'>:</span><span class='hs-conid'>SList</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>314: </span>        <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-conop'>:</span><span class='hs-conid'>SListN</span> <span class='hs-keyword'>_</span> <span class='hs-keyword'>{1 + size f}</span>
<span class=hs-linenum>315: </span>        <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-conop'>:</span><span class='hs-conid'>SList</span> <span class='hs-keyword'>_</span>
<span class=hs-linenum>316: </span>        <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>SListN</span> <span class='hs-keyword'>_</span> <span class='hs-keyword'>{size f + size b + size a}</span>
<span class=hs-linenum>317: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>318: </span><a class=annot href="#"><span class=annottext>forall a.
x1:(LazyQueue.SList a)
-&gt; x2:{v : (LazyQueue.SList a) | size v == 1 + size x1}
-&gt; x3:(LazyQueue.SList a)
-&gt; {v : (LazyQueue.SList a) | size v == size x1 + size x2 + size x3}</span><span class='hs-definition'>rot</span></a> <a class=annot href="#"><span class=annottext>(LazyQueue.SList a)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | size v == 1 + size f}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>(LazyQueue.SList a)</span><span class='hs-varid'>a</span></a>
<span class=hs-linenum>319: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>x1:(LazyQueue.SList a)
-&gt; {v : GHC.Types.Int | v == size x1 &amp;&amp; v &gt;= 0}</span><span class='hs-varid'>size</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == f}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int
-&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Bool | Prop v &lt;=&gt; x1 == v}</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == (0  :  int)}</span><span class='hs-num'>0</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | size v &gt; 0} -&gt; a</span><span class='hs-varid'>hd</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == b &amp;&amp; size v == 1 + size f}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>a
-&gt; x2:(LazyQueue.SList a)
-&gt; {v : (LazyQueue.SList a) | size v == size v + 1}</span><span class='hs-varop'>`cons`</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == a}</span><span class='hs-varid'>a</span></a>
<span class=hs-linenum>320: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | size v &gt; 0} -&gt; a</span><span class='hs-varid'>hd</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == f}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>a
-&gt; x2:(LazyQueue.SList a)
-&gt; {v : (LazyQueue.SList a) | size v == size v + 1}</span><span class='hs-varop'>`cons`</span></a> <a class=annot href="#"><span class=annottext>forall a.
x1:(LazyQueue.SList a)
-&gt; x2:{v : (LazyQueue.SList a) | size v == 1 + size x1}
-&gt; x3:(LazyQueue.SList a)
-&gt; {v : (LazyQueue.SList a) | size v == size x1 + size x2 + size x3}</span><span class='hs-varid'>rot</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:{v : (LazyQueue.SList a) | size v &gt; 0}
-&gt; {v : (LazyQueue.SList a) | size v == size x1 - 1}</span><span class='hs-varid'>tl</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == f}</span><span class='hs-varid'>f</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:{v : (LazyQueue.SList a) | size v &gt; 0}
-&gt; {v : (LazyQueue.SList a) | size v == size x1 - 1}</span><span class='hs-varid'>tl</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == b &amp;&amp; size v == 1 + size f}</span><span class='hs-varid'>b</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | size v &gt; 0} -&gt; a</span><span class='hs-varid'>hd</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == b &amp;&amp; size v == 1 + size f}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>a
-&gt; x2:(LazyQueue.SList a)
-&gt; {v : (LazyQueue.SList a) | size v == size v + 1}</span><span class='hs-varop'>`cons`</span></a> <a class=annot href="#"><span class=annottext>{v : (LazyQueue.SList a) | v == a}</span><span class='hs-varid'>a</span></a><span class='hs-layout'>)</span>
</pre>

Conclusion
----------

Well there you have it; Okasaki's beautiful lazy Queue, with the
invariants easily expressed and checked with LiquidHaskell. I find
this example particularly interesting because the refinements express
invariants that are critical for efficiency, and furthermore the code
introspects on the `size` in order to guarantee the invariants.  Plus,
it's just marginally more complicated than `append` and so, (I hope!)
was easy to follow.



[okasaki95]: http://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/jfp95queue.pdf

[queue-wiki]: http://en.wikipedia.org/wiki/Queue_%28abstract_data_type%29
