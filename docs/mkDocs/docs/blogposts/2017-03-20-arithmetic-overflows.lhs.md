---
layout: post
title: Arithmetic Overflows
date: 2017-03-20
author: Ranjit Jhala
published: true
comments: true
tags:
   - basic
demo: overflow.hs
---


Computers are great at crunching numbers.
However, if programmers aren't careful, their
machines can end up biting off more than
they can chew: simple arithmetic operations
over very large (or very tiny) inputs can
*overflow* leading to bizarre crashes
or vulnerabilities. For example,
[Joshua Bloch's classic post][bloch]
argues that nearly all binary searches
are broken due to integer overflows.
Lets see how we can teach LiquidHaskell
to spot such overflows.

<!-- more -->

<div class="hidden">

<pre><span class=hs-linenum>30: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Bounded</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>31: </span>
<span class=hs-linenum>32: </span><span class='hs-keyword'>import</span>           <span class='hs-conid'>Control</span><span class='hs-varop'>.</span><span class='hs-conid'>Exception</span> <span class='hs-layout'>(</span><span class='hs-varid'>assert</span><span class='hs-layout'>)</span>
<span class=hs-linenum>33: </span><span class='hs-keyword'>import</span>           <span class='hs-conid'>Prelude</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-conid'>Num</span> <span class='hs-layout'>(</span><span class='hs-keyglyph'>..</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>34: </span><span class='hs-keyword'>import</span> <span class='hs-keyword'>qualified</span> <span class='hs-conid'>Prelude</span>
<span class=hs-linenum>35: </span>
<span class=hs-linenum>36: </span><span class='hs-definition'>plusStrict</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>37: </span><span class='hs-definition'>plusLazy</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>38: </span><span class='hs-definition'>mono</span>       <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
</pre>
</div>

1. The Problem
--------------


LiquidHaskell, like some programmers, likes to make believe
that `Int` represents the set of integers. For example, you
might define a function `plus` as:


<pre><span class=hs-linenum>51: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>plus</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v == x + y}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>52: </span><span class='hs-definition'>plus</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>53: </span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2}</span><span class='hs-definition'>plus</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : Int | v == y}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2}</span><span class='hs-conid'>Prelude</span></a><span class='hs-varop'>.+</span> <span class='hs-varid'>y</span>
</pre>

The output type of the function states that the returned value
is equal to the \emph{logical} result of adding the two inputs.

The above signature lets us "prove" facts like addition by one
yields a bigger number:


<pre><span class=hs-linenum>63: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>monoPlus</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Bool</span> <span class='hs-keyword'>| v &lt;=&gt; true }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>64: </span><span class='hs-definition'>monoPlus</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>65: </span><a class=annot href="#"><span class=annottext>Int -&gt; {v : Bool | v &lt;=&gt; true}</span><span class='hs-definition'>monoPlus</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : Int | v == x}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2} | v == Bounded.plus}</span><span class='hs-varid'>plus</span></a> <span class='hs-varid'>x</span> <span class='hs-num'>1</span>
</pre>

Unfortunately, the signature for plus and hence, the above
"fact" are both lies.

LH _checks_ `plus` as the same signature is _assumed_
for the primitive `Int` addition operator `Prelude.+`.
LH has to assume _some_ signature for this "foreign"
machine operation, and by default, LH assumes that
machine addition behaves like logical addition.

However, this assumption, and its consequences are
only true upto a point:

```haskell
λ>  monoPlus 0
True
λ>  monoPlus 100
True
λ>  monoPlus 10000
True
λ>  monoPlus 1000000
True
```

Once we get to `maxBound` at the very edge of `Int`,
a tiny bump is enough to send us tumbling backwards
into a twilight zone.

```haskell
λ> monoPlus maxBound
False

λ> plus maxBound 1
-9223372036854775808
```

2. Keeping Int In Their Place
-----------------------------

The news isn't all bad: the glass half full
view is that for "reasonable" values
like 10, 100, 10000 and 1000000, the
machine's arithmetic _is_ the same as
logical arithmetic. Lets see how to impart
this wisdom to LH. We do this in two steps:
define the *biggest* `Int` value, and then,
use this value to type the arithmetic operations.

**A. The Biggest Int**

First, we need a way to talk about
"the edge" -- i.e. the largest `Int`
value at which overflows occur.

We could use the concrete number

```haskell
λ> maxBound :: Int
9223372036854775807
```

However, instead of hardwiring a particular number,
a more general strategy is to define a symbolic
constant `maxInt` to represent _any_ arbitrary
overflow value and thus, make the type checking
robust to different machine integer widths.


<pre><span class=hs-linenum>135: </span><span class='hs-comment'>-- defines an Int constant called `maxInt`</span>
<span class=hs-linenum>136: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
</pre>

To tell LH that `maxInt` is the "biggest" `Int`,
we write a predicate that describes values bounded
by `maxInt`:


<pre><span class=hs-linenum>144: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>Bounded</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span> <span class='hs-varop'>&lt;</span> <span class='hs-conid'>N</span> <span class='hs-varop'>+</span> <span class='hs-varid'>maxInt</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-conid'>N</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>maxInt</span> <span class='hs-keyword'>@-}</span>
</pre>

Thus, `Bounded n` means that the number `n` is in
the range `[-maxInt, maxInt]`.

**B.  Bounded Machine Arithmetic**

Next, we can assign the machine arithmetic operations
types that properly capture the possibility of arithmetic
overflows. Here are _two_ possible specifications.

**Strict: Thou Shalt Not Overflow** A _strict_ specification
simply prohibits any overflow:


<pre><span class=hs-linenum>160: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>plusStrict</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-keyword'>{Int|Bounded(x+y)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span><span class='hs-keyword'>|v = x+y}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>161: </span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:{y : Int | 0 &lt; (x1 + y) + maxInt
                        &amp;&amp; x1 + y &lt; maxInt} -&gt; {v : Int | v == x1 + x2}</span><span class='hs-definition'>plusStrict</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{y : Int | 0 &lt; (x + y) + maxInt
           &amp;&amp; x + y &lt; maxInt}</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : Int | 0 &lt; (x + v) + maxInt
           &amp;&amp; x + v &lt; maxInt
           &amp;&amp; v == y}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2}</span><span class='hs-conid'>Prelude</span></a><span class='hs-varop'>.+</span> <span class='hs-varid'>y</span>
</pre>

The inputs `x` and `y` _must_ be such that the result is `Bounded`,
and in that case, the output value is indeed their logical sum.

**Lazy: Overflow at Thine Own Risk** Instead, a _lazy_
specification could permit overflows but gives no
guarantees about the output when they occur.


<pre><span class=hs-linenum>172: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>plusLazy</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span><span class='hs-keyword'>|Bounded(x+y) =&gt; v = x+y}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>173: </span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | 0 &lt; (x1 + x2) + maxInt
                               &amp;&amp; x1 + x2 &lt; maxInt =&gt; v == x1 + x2}</span><span class='hs-definition'>plusLazy</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : Int | v == y}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2}</span><span class='hs-conid'>Prelude</span></a><span class='hs-varop'>.+</span> <span class='hs-varid'>y</span>
</pre>

The lazy specification says that while `plusLazy`
can be called with any values you like, the
result is the logical sum
*only if there is no overflow*.


To understand the difference between the two
specifications, lets revisit the `monoPlus`
property using the new machine-arithmetic
sensitive signatures:


<pre><span class=hs-linenum>188: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>monoPlusStrict</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Bool</span> <span class='hs-keyword'>| v &lt;=&gt; true }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>189: </span><a class=annot href="#"><span class=annottext>Int -&gt; {v : Bool | v &lt;=&gt; true}</span><span class='hs-definition'>monoPlusStrict</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : Int | v == x}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class=hs-error><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | 0 &lt; (x1 + v) + maxInt
                             &amp;&amp; x1 + v &lt; maxInt} -&gt; {v : Int | v == x1 + x2} | v == Bounded.plusStrict}</span><span class='hs-varid'>plusStrict</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-varid'>x</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>1</span></span>
<span class=hs-linenum>190: </span>
<span class=hs-linenum>191: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>monoPlusLazy</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Bool</span> <span class='hs-keyword'>| v &lt;=&gt; true }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>192: </span><a class=annot href="#"><span class=annottext>Int -&gt; {v : Bool | v &lt;=&gt; true}</span><span class='hs-definition'>monoPlusLazy</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>{v : Int | v == x}</span><span class='hs-varid'>x</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : Int | 0 &lt; (x1 + x2) + maxInt
                                    &amp;&amp; x1 + x2 &lt; maxInt =&gt; v == x1 + x2} | v == Bounded.plusLazy}</span><span class='hs-varid'>plusLazy</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-varid'>x</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>1</span></span>
</pre>

Both are rejected by LH, since, as we saw earlier,
the functions _do not_ always evaluate to `True`.
However, in the strict version the error is at the
possibly overflowing call to `plusStrict`.
In the lazy version, the call to `plusLazy` is
accepted, but as the returned value is some
arbitrary `Int` (not the logical `x+1`), the
comparison may return `False` hence the output
is not always `True`.

**Exercise:** Can you fix the specification
for `monoPlusStrict` and `monoPlusLazy` to
get LH to verify the implementation?


3. A Typeclass for Machine Arithmetic
-------------------------------------

Its a bit inconvenient to write `plusStrict` and `plusLazy`,
and really, we'd just like to write `+` and `-` and so on.
We can do so, by tucking the above specifications into
a _bounded numeric_ typeclass whose signatures capture machine
arithmetic. First, we define a `BoundedNum` variant of `Num`


<pre><span class=hs-linenum>220: </span><span class='hs-keyword'>class</span> <span class='hs-conid'>BoundedNum</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>221: </span>  <span class='hs-layout'>(</span><span class='hs-varop'>+</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>222: </span>  <span class='hs-layout'>(</span><span class='hs-comment'>-</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>223: </span>  <span class='hs-comment'>-- other operations ...</span>
</pre>

and now, we can define its `Int` instance just as wrappers
around the `Prelude` operations:


<pre><span class=hs-linenum>230: </span><span class='hs-keyword'>instance</span> <span class='hs-conid'>BoundedNum</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>231: </span>  <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:{y : Int | 0 &lt; (x1 + y) + maxInt
                        &amp;&amp; x1 + y &lt; maxInt} -&gt; {v : Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{y : Int | 0 &lt; (x + y) + maxInt
           &amp;&amp; x + y &lt; maxInt}</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : Int | 0 &lt; (x + v) + maxInt
           &amp;&amp; x + v &lt; maxInt
           &amp;&amp; v == y}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2}</span><span class='hs-conid'>Prelude</span></a><span class='hs-varop'>.+</span> <span class='hs-varid'>y</span>
<span class=hs-linenum>232: </span>  <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:{y : Int | 0 &lt; (x1 - y) + maxInt
                        &amp;&amp; x1 - y &lt; maxInt} -&gt; {v : Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{y : Int | 0 &lt; (x - y) + maxInt
           &amp;&amp; x - y &lt; maxInt}</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : Int | 0 &lt; (x - v) + maxInt
           &amp;&amp; x - v &lt; maxInt
           &amp;&amp; v == y}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 - x2}</span><span class='hs-conid'>Prelude</span></a><span class='hs-varop'>.-</span> <span class='hs-varid'>y</span>
</pre>

Finally, we can tell LH that the above above instance obeys the
(strict) specifications for machine arithmetic:


<pre><span class=hs-linenum>239: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>instance</span> <span class='hs-conid'>BoundedNum</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>240: </span>      <span class='hs-varop'>+</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-keyword'>{Int | Bounded (x+y)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v == x+y }</span><span class='hs-layout'>;</span>
<span class=hs-linenum>241: </span>      <span class='hs-comment'>-</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-keyword'>{Int | Bounded (x-y)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v == x-y }</span>
<span class=hs-linenum>242: </span>  <span class='hs-keyword'>@-}</span>
</pre>

With the above instance in scope, we can just use the plain `+`
operator and have LH flag potential overflows:


<pre><span class=hs-linenum>249: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>mono</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Bool</span> <span class='hs-keyword'>| v &lt;=&gt; true}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>250: </span><a class=annot href="#"><span class=annottext>Int -&gt; {v : Bool | v &lt;=&gt; true}</span><span class='hs-definition'>mono</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : Int | v == x}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class=hs-error><a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>x</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-varop'>+</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>1</span></span>
</pre>


4. An Application: Binary Search
--------------------------------

The above seems a bit paranoid. Do overflows _really_ matter?
And if they do, is it really practical to check for them using
the above?

[Joshua Bloch's][bloch] famous article describes a
tricky overflow bug in an implementation of binary-search
that lay hidden in plain sight in classic textbooks and his
own implementation in the JDK for nearly a decade.
Gabriel Gonzalez wrote a lovely [introduction to LH][lh-gonzalez]
using binary-search as an example, and a careful reader
[pointed out][lh-overflow-reddit] that it had the same
overflow bug!

Lets see how we might spot and fix such bugs using `BoundedNum`. 
(_Hover over the images to animate_.)

<div class="row">
<div class="col-md-4">
**A. Off by One** Lets begin by just using
the default `Num Int` which ignores overflow.
As Gabriel explains, LH flags a bunch of errors
if we start the search with `loop x v 0 n` as
the resulting search can access `v` at any
index between `0` and `n` inclusive, which
may lead to an out of bounds at `n`.
We can fix the off-by-one by correcting the
upper bound to `n-1`, at which point LH
reports the code free of errors.
</div>

<div class="col-md-8">
<img id="splash-binarySearch-A"
     class="center-block anim"
     png="../../static/img/splash-binarySearch-A.png"
     src="../../static/img/splash-binarySearch-A.png">
</div>
</div>

<br>


<div class="row">
<div class="col-md-8">
<img id="splash-binarySearch-B"
     class="center-block anim"
     png="../../static/img/splash-binarySearch-B.png"
     src="../../static/img/splash-binarySearch-B.png">
</div>

<div class="col-md-4">
**B. Lots of Overflows** To spot arithmetic overflows, we need
only hide the default `Prelude` and instead import the `BoundedNum`
instance described above. Upon doing so, LH flags a whole bunch of
potential errors -- essentially *all* the arithmetic operations which
seems rather dire!
</div>
</div>


<div class="row">
<div class="col-md-4">
**C. Vector Sizes are Bounded** Of course, things
aren't _so_ bad. LH is missing the information that
the size of any `Vector` must be `Bounded`. Once we
inform LH about this invariant with the
[`using` directive][lh-invariants], it infers that
as the `lo` and `hi` indices are upper-bounded by
the `Vector`'s size, all the arithmetic on them is
also `Bounded` and hence, free of overflows.
</div>

<div class="col-md-8">
<img id="splash-binarySearch-C"
     class="center-block anim"
     png="../../static/img/splash-binarySearch-C.png"
     src="../../static/img/splash-binarySearch-C.png">
</div>
</div>

<br>

<div class="row">
<div class="col-md-8">
<img id="splash-binarySearch-D"
     class="center-block anim"
     png="../../static/img/splash-binarySearch-D.png"
     src="../../static/img/splash-binarySearch-D.png">
</div>

<div class="col-md-4">
**D. Staying In The Middle**
Well, *almost* all. The one pesky pink highlight that
remains is exactly the bug that Bloch made famous. Namely:
the addition used to compute the new midpoint between `lo`
and `hi` could overflow e.g. if the array was large and both
those indices were near the end. To ensure the machine doesn't
choke, we follow Bloch's suggestion and re-jigger the computation
to instead compute the midpoint by splitting the difference
between `hi` and `lo`! the code is now free of arithmetic
overflows and truly memory safe.
</div>
</div>


[lh-invariants]: https://github.com/ucsd-progsys/liquidhaskell/blob/develop/README.md#invariants
[lh-gonzalez]: http://www.haskellforall.com/2015/12/compile-time-memory-safety-using-liquid.html
[bloch]: https://research.googleblog.com/2006/06/extra-extra-read-all-about-it-nearly.html
[lh-overflow-reddit]: https://www.reddit.com/r/haskell/comments/3ysh9k/haskell_for_all_compiletime_memory_safety_using/cyg8g60/
