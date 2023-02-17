---
layout: post
title: Refinement Types 101
date: 2013-01-01 16:12
author: Ranjit Jhala
published: true
comments: true
tags:
   - basic
demo: refinements101.hs
---


One of the great things about Haskell is its brainy type system that
allows one to enforce a variety of invariants at compile time, thereby
nipping a large swathe of run-time errors in the bud. Refinement types
allow us to use modern logic solvers (*aka* SAT and SMT engines) to
dramatically extend the scope of invariants that can be statically
verified.

What is a Refinement Type?
--------------------------

In a nutshell, 

<blockquote><p>
Refinement Types = Types + Logical Predicates
</p></blockquote>

That is, refinement types allow us to decorate types with 
*logical predicates* (think *boolean-valued* Haskell expressions) 
which constrain the set of values described by the type, and hence 
allow us to specify sophisticated invariants of the underlying values. 

Say what? 

<!-- more -->

(Btw, *click the title* to demo LiquidHaskell on the code in this article)


<pre><span class=hs-linenum>42: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Intro</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>43: </span>
<span class=hs-linenum>44: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span>  <span class='hs-layout'>(</span><span class='hs-varid'>liquidAssert</span><span class='hs-layout'>)</span>
</pre>

Let us jump right in with a simple example, the number `0 :: Int`. 
As far as Haskell is concerned, the number is simply an `Int` (lets not
worry about things like `Num` for the moment). So are `2`, `7`, and 
`904`. With refinements we can dress up these values so that they 
stand apart. For example, consider the binder


<pre><span class=hs-linenum>54: </span><span class='hs-definition'>zero'</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>55: </span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (0 &lt;= VV)}</span><span class='hs-definition'>zero'</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(GHC.Prim.Int#) -&gt; {VV : (GHC.Types.Int) | (VV = (x  :  int))}</span><span class='hs-num'>0</span></a>
</pre>

We can ascribe to the variable `zero'` the refinement type


<pre><span class=hs-linenum>61: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>zero'</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| 0 &lt;= v}</span> <span class='hs-keyword'>@-}</span>
</pre>

which is simply the basic type `Int` dressed up with a predicate.
The binder `v` is called the *value variable*, and so the above denotes 
the set of `Int` values which are greater than `0`. Of course, we can
attach other predicates to the above value, for example

**Note:** We will use `@`-marked comments to write refinement type 
annotations the Haskell source file, making these types, quite literally,
machine-checked comments!



<pre><span class=hs-linenum>75: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>zero''</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| (0 &lt;= v &amp;&amp; v &lt; 100) }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>76: </span><span class='hs-definition'>zero''</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>77: </span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &lt; 100),(0 &lt;= VV)}</span><span class='hs-definition'>zero''</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(GHC.Prim.Int#) -&gt; {VV : (GHC.Types.Int) | (VV = (x  :  int))}</span><span class='hs-num'>0</span></a>
</pre>

which states that the number is in the range `0` to `100`, or


<pre><span class=hs-linenum>83: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>zero'''</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| ((v mod 2) = 0) }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>84: </span><span class='hs-definition'>zero'''</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>85: </span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | ((VV mod 2) = 0)}</span><span class='hs-definition'>zero'''</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(GHC.Prim.Int#) -&gt; {VV : (GHC.Types.Int) | (VV = (x  :  int))}</span><span class='hs-num'>0</span></a>
</pre>

where `mod` is the *modulus* operator in the refinement logic. Thus, the type
above states that zero is an *even* number.

We can also use a singleton type that precisely describes the constant


<pre><span class=hs-linenum>94: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>zero''''</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = 0 }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>95: </span><span class='hs-definition'>zero''''</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>96: </span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = 0)}</span><span class='hs-definition'>zero''''</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(GHC.Prim.Int#) -&gt; {VV : (GHC.Types.Int) | (VV = (x  :  int))}</span><span class='hs-num'>0</span></a>
</pre>

(Aside: we use a different names `zero'`, `zero''` etc. for a silly technical 
reason -- LiquidHaskell requires that we ascribe a single refinement type to 
a top-level name.)

Finally, we could write a single type that captures all the properties above:


<pre><span class=hs-linenum>106: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>zero</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| ((0 &lt;= v) &amp;&amp; ((v mod 2) = 0) &amp;&amp; (v &lt; 100)) }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>107: </span><span class='hs-definition'>zero</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>108: </span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | ((VV mod 2) = 0),(VV &lt; 100),(0 &lt;= VV)}</span><span class='hs-definition'>zero</span></a>     <span class='hs-keyglyph'>=</span>  <a class=annot href="#"><span class=annottext>x:(GHC.Prim.Int#) -&gt; {VV : (GHC.Types.Int) | (VV = (x  :  int))}</span><span class='hs-num'>0</span></a>
</pre>

The key points are:

1. A refinement type is just a type *decorated* with logical predicates.
2. A value can have *different* refinement types that describe different properties.
3. If we *erase* the green bits (i.e. the logical predicates) we get back *exactly* 
   the usual Haskell types that we know and love.
4. A vanilla Haskell type, say `Int` has the trivial refinement `true` i.e. is 
   really `{v: Int | true}`.

We have built a refinement type-based verifier called LiquidHaskell. 
Lets see how we can use refinement types to specify and verify interesting 
program invariants in LiquidHaskell.

Writing Safety Specifications
-----------------------------

We can use refinement types to write various kinds of more interesting
safety specifications.

First, we can write a wrapper around the usual `error` function 


<pre><span class=hs-linenum>133: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>error'</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>String</span> <span class='hs-keyword'>| false }</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>134: </span><span class='hs-definition'>error'</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>String</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>135: </span><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | false} -&gt; a</span><span class='hs-definition'>error'</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[(GHC.Types.Char)] -&gt; a</span><span class='hs-varid'>error</span></a>
</pre>

The interesting thing about the type signature for `error'` is that the
input type has the refinement `false`. That is, the function must only be
called with `String`s that satisfy the predicate `false`. Of course, there
are *no* such values. Thus, a program containing the above function
typechecks *exactly* when LiquidHaskell can prove that the function
`error'` is *never called*.

Next, we can use refinements to encode arbitrary programmer-specified 
**assertions** by defining a function


<pre><span class=hs-linenum>149: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>lAssert</span>     <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Bool</span> <span class='hs-keyword'>| (Prop v)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>150: </span><span class='hs-definition'>lAssert</span>         <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Bool</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>151: </span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV]))} -&gt; a -&gt; a</span><span class='hs-definition'>lAssert</span></a> <span class='hs-conid'>True</span>  <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>152: </span><span class='hs-definition'>lAssert</span> <span class='hs-conid'>False</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | false} -&gt; {VV : a | false}</span><span class='hs-varid'>error'</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"lAssert failure"</span></a> 
</pre>

In the refinement, `(Prop v)` denotes the Haskell `Bool` value `v` 
interpreted as a logical predicate. In other words, the input type for 
this function specifies that the function must *only* be called with
the value `True`.


Refining Function Types : Preconditions
---------------------------------------

Lets use the above to write a *divide* function that *only accepts* non-zero
denominators. 


<pre><span class=hs-linenum>168: </span><span class='hs-definition'>divide</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>169: </span><a class=annot href="#"><span class=annottext>(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV != 0)} -&gt; (GHC.Types.Int)</span><span class='hs-definition'>divide</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | false} -&gt; {VV : (GHC.Types.Int) | false}</span><span class='hs-varid'>error'</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"divide by zero"</span></a>
<span class=hs-linenum>170: </span><span class='hs-definition'>divide</span> <span class='hs-varid'>n</span> <span class='hs-varid'>d</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = n)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x / y))}</span><span class='hs-varop'>`div`</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV != 0)}</span><span class='hs-varid'>d</span></a>
</pre>

We can specify that the non-zero denominator *precondition* with a suitable 
refinement on the *input* component of the function's type 


<pre><span class=hs-linenum>177: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>divide</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| v != 0 }</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
</pre>

How *does* LiquidHaskell verify the above function? 

The key step is that LiquidHaskell deduces that the expression 
`"divide by zero"` is not merely of type `String`, but in fact 
has the the refined type `{v:String | false}` *in the context* 
in which the call to `error'` occurs.

LiquidHaskell arrives at this conclusion by using the fact that 
in the first equation for `divide` the *denominator* parameter 
is in fact `0 :: {v: Int | v = 0}` which *contradicts* the 
precondition (i.e. input) type.

In other words, LiquidHaskell deduces by contradiction, that 
the first equation is **dead code** and hence `error'` will 
not be called at run-time.

If you are paranoid, you can put in an explicit assertion


<pre><span class=hs-linenum>199: </span><span class='hs-definition'>divide'</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>200: </span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | false}
-&gt; {VV : (GHC.Types.Int) | false} -&gt; {VV : (GHC.Types.Int) | false}</span><span class='hs-definition'>divide'</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | false}</span><span class='hs-varid'>n</span></a> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | false} -&gt; {VV : (GHC.Types.Int) | false}</span><span class='hs-varid'>error'</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"divide by zero"</span></a>
<span class=hs-linenum>201: </span><span class='hs-definition'>divide'</span> <span class='hs-varid'>n</span> <span class='hs-varid'>d</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV]))}
-&gt; {VV : (GHC.Types.Int) | false} -&gt; {VV : (GHC.Types.Int) | false}</span><span class='hs-varid'>lAssert</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | false}</span><span class='hs-varid'>d</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (GHC.Types.Int) | false}
-&gt; y:{VV : (GHC.Types.Int) | false}
-&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x != y))}</span><span class='hs-varop'>/=</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | false} -&gt; {VV : (GHC.Types.Int) | false})
-&gt; {VV : (GHC.Types.Int) | false} -&gt; {VV : (GHC.Types.Int) | false}</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | false}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x / y))}</span><span class='hs-varop'>`div`</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | false}</span><span class='hs-varid'>d</span></a>
</pre>

and LiquidHaskell will verify the assertion (by verifying the call to
`lAssert`) for you.

Refining Function Types : Postconditions
----------------------------------------

Next, lets see how we can use refinements to describe the *outputs* of a
function. Consider the following simple *absolute value* function


<pre><span class=hs-linenum>214: </span><span class='hs-definition'>abz</span>               <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>215: </span><a class=annot href="#"><span class=annottext>(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (0 &lt;= VV)}</span><span class='hs-definition'>abz</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a> <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt; y))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = n)}</span><span class='hs-varid'>n</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = n)}</span><span class='hs-varid'>n</span></a>
<span class=hs-linenum>216: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x - y))}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = n)}</span><span class='hs-varid'>n</span></a>
</pre>

We can use a refinement on the output type to specify that the function 
returns non-negative values


<pre><span class=hs-linenum>223: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>abz</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| 0 &lt;= v }</span> <span class='hs-keyword'>@-}</span>
</pre>

LiquidHaskell *verifies* that `abz` indeed enjoys the above type by
deducing that `n` is trivially non-negative when `0 < n` and that in 
the `otherwise` case, i.e. when `not (0 < n)` the value `0 - n` is
indeed non-negative (lets not worry about underflows for the moment.)
LiquidHaskell is able to automatically make these arithmetic deductions
by using an [SMT solver](https://github.com/Z3Prover/z3) which has decision
built-in procedures for arithmetic, to reason about the logical
refinements.



Putting It All Together
-----------------------

Lets wrap up this introduction with a simple `truncate` function 
that connects all the dots. 


<pre><span class=hs-linenum>244: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>truncate</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>245: </span><a class=annot href="#"><span class=annottext>(GHC.Types.Int) -&gt; (GHC.Types.Int) -&gt; (GHC.Types.Int)</span><span class='hs-definition'>truncate</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>max</span></a>  
<span class=hs-linenum>246: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i'),(0 &lt;= VV)}</span><span class='hs-varid'>i'</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (GHC.Types.Int) | (VV &gt;= 0),(VV &gt;= zero''''),(0 &lt;= VV)}
-&gt; y:{VV : (GHC.Types.Int) | (VV &gt;= 0),(VV &gt;= zero''''),(0 &lt;= VV)}
-&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = max'),(0 &lt;= VV)}</span><span class='hs-varid'>max'</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i)}</span><span class='hs-varid'>i</span></a>
<span class=hs-linenum>247: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = max'),(0 &lt;= VV)}</span><span class='hs-varid'>max'</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (&amp;&amp; [(x &gt;= 0); (y &gt;= 0)] =&gt; (VV &gt;= 0))}</span><span class='hs-varop'>*</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV != 0)} -&gt; (GHC.Types.Int)</span><span class='hs-varop'>`divide`</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i'),(0 &lt;= VV)}</span><span class='hs-varid'>i'</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>248: </span>    <span class='hs-keyword'>where</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (0 &lt;= VV)}</span><span class='hs-varid'>i'</span></a>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (0 &lt;= VV)}</span><span class='hs-varid'>abz</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i)}</span><span class='hs-varid'>i</span></a>
<span class=hs-linenum>249: </span>          <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (0 &lt;= VV)}</span><span class='hs-varid'>max'</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (0 &lt;= VV)}</span><span class='hs-varid'>abz</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = max)}</span><span class='hs-varid'>max</span></a> 
</pre>

`truncate i n` simply returns `i` if its absolute value is less the
upper bound `max`, and otherwise *truncates* the value at the maximum.
LiquidHaskell verifies that the use of `divide` is safe by inferring that 
at the call site

1. `i' > max'` from the branch condition.
2. `0 <= i'`   from the `abz` postcondition (hover mouse over `i'`).
3. `0 <= max'` from the `abz` postcondition (hover mouse over `max'`).

From the above, LiquidHaskell infers that `i' != 0`. That is, at the
call site `i' :: {v: Int | v != 0}`, thereby satisfying the
precondition for `divide` and verifying that the program has no pesky 
divide-by-zero errors. Again, if you *really* want to make sure, put 
in an assertion


<pre><span class=hs-linenum>268: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>truncate'</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>269: </span><a class=annot href="#"><span class=annottext>(GHC.Types.Int) -&gt; (GHC.Types.Int) -&gt; (GHC.Types.Int)</span><span class='hs-definition'>truncate'</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>max</span></a>  
<span class=hs-linenum>270: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i'),(0 &lt;= VV)}</span><span class='hs-varid'>i'</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (GHC.Types.Int) | (VV &gt;= 0),(VV &gt;= zero''''),(0 &lt;= VV)}
-&gt; y:{VV : (GHC.Types.Int) | (VV &gt;= 0),(VV &gt;= zero''''),(0 &lt;= VV)}
-&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = max'),(0 &lt;= VV)}</span><span class='hs-varid'>max'</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i)}</span><span class='hs-varid'>i</span></a>
<span class=hs-linenum>271: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV]))}
-&gt; (GHC.Types.Int) -&gt; (GHC.Types.Int)</span><span class='hs-varid'>lAssert</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i'),(0 &lt;= VV)}</span><span class='hs-varid'>i'</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (GHC.Types.Int) | (VV &gt;= 0),
                          (VV &gt;= zero''''),
                          (0 &lt;= VV),
                          (VV &lt;= i')}
-&gt; y:{VV : (GHC.Types.Int) | (VV &gt;= 0),
                             (VV &gt;= zero''''),
                             (0 &lt;= VV),
                             (VV &lt;= i')}
-&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x != y))}</span><span class='hs-varop'>/=</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>((GHC.Types.Int) -&gt; (GHC.Types.Int))
-&gt; (GHC.Types.Int) -&gt; (GHC.Types.Int)</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = max'),(0 &lt;= VV)}</span><span class='hs-varid'>max'</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (&amp;&amp; [(x &gt;= 0); (y &gt;= 0)] =&gt; (VV &gt;= 0))}</span><span class='hs-varop'>*</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV != 0)} -&gt; (GHC.Types.Int)</span><span class='hs-varop'>`divide`</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i'),(0 &lt;= VV)}</span><span class='hs-varid'>i'</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>272: </span>    <span class='hs-keyword'>where</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (0 &lt;= VV)}</span><span class='hs-varid'>i'</span></a>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (0 &lt;= VV)}</span><span class='hs-varid'>abz</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i)}</span><span class='hs-varid'>i</span></a>
<span class=hs-linenum>273: </span>          <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (0 &lt;= VV)}</span><span class='hs-varid'>max'</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (0 &lt;= VV)}</span><span class='hs-varid'>abz</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = max)}</span><span class='hs-varid'>max</span></a> 
</pre>

and *lo!* LiquidHaskell will verify it for you.

Modular Verification
--------------------

Incidentally, note the `import` statement at the top. Rather than rolling
our own `lAssert` we can import and use a pre-defined version `liquidAssert`
defined in an external [module](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/liquid-prelude/src/Language/Haskell/Liquid/Prelude.hs)


<pre><span class=hs-linenum>286: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>truncate''</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>287: </span><a class=annot href="#"><span class=annottext>(GHC.Types.Int) -&gt; (GHC.Types.Int) -&gt; (GHC.Types.Int)</span><span class='hs-definition'>truncate''</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>max</span></a>  
<span class=hs-linenum>288: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i'),(0 &lt;= VV)}</span><span class='hs-varid'>i'</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (GHC.Types.Int) | (VV &gt;= 0),(VV &gt;= zero''''),(0 &lt;= VV)}
-&gt; y:{VV : (GHC.Types.Int) | (VV &gt;= 0),(VV &gt;= zero''''),(0 &lt;= VV)}
-&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = max'),(0 &lt;= VV)}</span><span class='hs-varid'>max'</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i)}</span><span class='hs-varid'>i</span></a>
<span class=hs-linenum>289: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Bool) | (? Prop([VV]))}
-&gt; (GHC.Types.Int) -&gt; (GHC.Types.Int)</span><span class='hs-varid'>liquidAssert</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i'),(0 &lt;= VV)}</span><span class='hs-varid'>i'</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (GHC.Types.Int) | (VV &gt;= 0),
                          (VV &gt;= zero''''),
                          (0 &lt;= VV),
                          (VV &lt;= i')}
-&gt; y:{VV : (GHC.Types.Int) | (VV &gt;= 0),
                             (VV &gt;= zero''''),
                             (0 &lt;= VV),
                             (VV &lt;= i')}
-&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x != y))}</span><span class='hs-varop'>/=</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>((GHC.Types.Int) -&gt; (GHC.Types.Int))
-&gt; (GHC.Types.Int) -&gt; (GHC.Types.Int)</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = max'),(0 &lt;= VV)}</span><span class='hs-varid'>max'</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (&amp;&amp; [(x &gt;= 0); (y &gt;= 0)] =&gt; (VV &gt;= 0))}</span><span class='hs-varop'>*</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV != 0)} -&gt; (GHC.Types.Int)</span><span class='hs-varop'>`divide`</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i'),(0 &lt;= VV)}</span><span class='hs-varid'>i'</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>290: </span>    <span class='hs-keyword'>where</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (0 &lt;= VV)}</span><span class='hs-varid'>i'</span></a>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (0 &lt;= VV)}</span><span class='hs-varid'>abz</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = i)}</span><span class='hs-varid'>i</span></a>
<span class=hs-linenum>291: </span>          <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (0 &lt;= VV)}</span><span class='hs-varid'>max'</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (0 &lt;= VV)}</span><span class='hs-varid'>abz</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = max)}</span><span class='hs-varid'>max</span></a> 
</pre>

In fact, LiquidHaskell comes equipped with suitable refinements for
standard functions and it is easy to add refinements as we shall
demonstrate in subsequent articles.

Conclusion
----------

This concludes our quick introduction to Refinement Types and
LiquidHaskell. Hopefully you have some sense of how to 

1. **Specify** fine-grained properties of values by decorating their
   types with logical predicates.
2. **Encode** assertions, preconditions, and postconditions with suitable
   function types.
3. **Verify** semantic properties of code by using automatic logic engines 
   (SMT solvers) to track and establish the key relationships between 
   program values.


