---
layout: post
title: Abstracting Over Refinements
date: 2013-06-03 16:12
comments: true
author: Ranjit Jhala and Niki Vazou 
published: true 
tags: abstract-refinements
demo: absref101.hs
---

We've seen all sorts of interesting invariants that can be expressed with
refinement predicates. For example, whether a divisor is [non-zero][blog-dbz], 
the [dimension][blog-len] of lists, ensuring the safety of 
[vector indices][blog-vec] and reasoning about the [set][blog-set] of values
in containers and verifying their [uniqueness][blog-zip].
In each of these cases, we were working with *specific* refinement predicates
that described whatever property was of interest.

Today, (drumroll please), I want to unveil a brand new feature of
LiquidHaskell, which allows us to *abstract* over specific properties or
invariants, which significantly increases the expressiveness of the 
system, whilst still allowing our friend the SMT solver to carry 
out verification and inference automatically.

<!-- more -->


<pre><span class=hs-linenum>30: </span>
<span class=hs-linenum>31: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>MickeyMouse</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>32: </span>
<span class=hs-linenum>33: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span> <span class='hs-layout'>(</span><span class='hs-varid'>isEven</span><span class='hs-layout'>)</span>
</pre>

Pin The Specification On the Function 
-------------------------------------

Lets look at some tiny *mickey-mouse* examples to see why we may want
to abstract over refinements in the first place.

Consider the following monomorphic `max` function on `Int` values:


<pre><span class=hs-linenum>45: </span><span class='hs-definition'>maxInt</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> 
<span class=hs-linenum>46: </span><a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; Bool&gt;.
{VV : (GHC.Types.Int)&lt;p&gt; | true}
-&gt; {VV : (GHC.Types.Int)&lt;p&gt; | true}
-&gt; {VV : (GHC.Types.Int)&lt;p&gt; | true}</span><span class='hs-definition'>maxInt</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | ((papp1 p VV))}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | ((papp1 p VV))}</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>if</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | ((papp1 p VV)) &amp;&amp; (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (GHC.Types.Int) | ((papp1 p VV))}
-&gt; y:{VV : (GHC.Types.Int) | ((papp1 p VV))}
-&gt; {VV : (GHC.Types.Bool) | (((Prop VV)) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | ((papp1 p VV)) &amp;&amp; (VV == y)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyword'>then</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | ((papp1 p VV)) &amp;&amp; (VV == y)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyword'>else</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | ((papp1 p VV)) &amp;&amp; (VV == x)}</span><span class='hs-varid'>x</span></a> 
</pre>

 We could give `maxInt` many, quite different and incomparable refinement types like
<pre><span class=hs-linenum>50: </span><span class='hs-definition'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&gt;=</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&gt;=</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&gt;=</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span>
</pre>

or
<pre><span class=hs-linenum>54: </span><span class='hs-definition'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&lt;</span> <span class='hs-num'>10</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&lt;</span> <span class='hs-num'>10</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&lt;</span> <span class='hs-num'>10</span><span class='hs-layout'>}</span>
</pre>

or even 
<pre><span class=hs-linenum>58: </span><span class='hs-definition'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conid'>Even</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conid'>Even</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conid'>Even</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>

All of the above are valid. 

But which one is the *right* type? 

At this point, you might be exasperated for one of two reasons.

First, the type enthusiasts among you may cry out -- "What? Does this funny
refinement type system not have **principal types**?"

No. Or, to be precise, of course not!

Principal typing is a lovely feature that is one of the many 
reasons why Hindley-Milner is such a delightful sweet spot. 
Unfortunately, the moment one wants fancier specifications 
one must tearfully kiss principal typing good bye.

Oh well.

Second, you may very well say, "Yes yes, does it even matter? Just pick
one and get on with it already!"

Unfortunately, it matters quite a bit.

Suppose we had a refined type describing valid RGB values:


<pre><span class=hs-linenum>87: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>RGB</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-num'>0</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-layout'>(</span><span class='hs-varid'>v</span> <span class='hs-varop'>&lt;</span> <span class='hs-num'>256</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

Now, if I wrote a function that selected the larger, that is to say, the
more intense, of two RGB values, I would certainly like to check that it 
produced an RGB value!


<pre><span class=hs-linenum>95: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>intenser</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>RGB</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>RGB</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>RGB</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>96: </span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &lt; 256) &amp;&amp; (0 &lt;= VV)}
-&gt; {VV : (GHC.Types.Int) | (VV &lt; 256) &amp;&amp; (0 &lt;= VV)}
-&gt; {VV : (GHC.Types.Int) | (VV &lt; 256) &amp;&amp; (0 &lt;= VV)}</span><span class='hs-definition'>intenser</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &lt; 256) &amp;&amp; (0 &lt;= VV)}</span><span class='hs-varid'>c1</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &lt; 256) &amp;&amp; (0 &lt;= VV)}</span><span class='hs-varid'>c2</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; Bool&gt;.
{VV : (GHC.Types.Int)&lt;p&gt; | true}
-&gt; {VV : (GHC.Types.Int)&lt;p&gt; | true}
-&gt; {VV : (GHC.Types.Int)&lt;p&gt; | true}</span><span class='hs-varid'>maxInt</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == c1) &amp;&amp; (VV &lt; 256) &amp;&amp; (0 &lt;= VV)}</span><span class='hs-varid'>c1</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == c2) &amp;&amp; (VV &lt; 256) &amp;&amp; (0 &lt;= VV)}</span><span class='hs-varid'>c2</span></a>
</pre>

Well, guess what. The first type (with `v >= 0`) one would tell us that 
the output was non-negative, losing the upper bound. The second type (with
`v < 10`) would cause LiquidHaskell to bellyache about `maxInt` being 
called with improper arguments -- muttering darkly that an RGB value 
is not necesarily less than `10`. As for the third type ... well, you get the idea.

So alas, the choice of type *does* matter. 

 If we were clairvoyant, we would give `maxInt` a type like
<pre><span class=hs-linenum>108: </span><span class='hs-definition'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>RGB</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>RGB</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>RGB</span> 
</pre>

but of course, that has its own issues. ("What? I have to write a
*separate* function for picking the larger of two *4* digit numbers?!")

Defining Parametric Invariants 
------------------------------

Lets take a step back from the types, and turn to a spot of handwaving.

What's *really* going on with `maxInt`?

Well, the function returns *one of* its two arguments `x` and `y`. 

This means that if *both* arguments satisfy some property then the output
*must* satisfy that property, *regardless of what that property was!*

To teach LiquidHaskell to understand this notion of "regardless of
property" we introduce the idea of **abstracting over refinements**
or, if you prefer, parameterizing a type over its refinements.

In particular, we type `maxInt` as


<pre><span class=hs-linenum>133: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span><span class='hs-keyword'>@-}</span>
</pre>

Here, the definition says explicitly: *for any property* `p` that is a
property of `Int`, the function takes two inputs each of which satisfy `p`
and returns an output that satisfies `p`. That is to say, `Int<p>` is 
just an abbreviation for `{v:Int | (p v)}`

**Digression: Whither Decidability?** 
At first glance, it may appear that these abstract `p` have taken us into
the realm of higher-order logics, where we must leave decidable checking
and our faithful SMT companion at that door, and instead roll up our 
sleeves for interactive proofs (not that there's anything wrong with that!) 
Fortunately, that's not the case. We simply encode abstract refinements `p` 
as *uninterpreted function symbols* in the refinement logic. 

 Uninterpreted functions are special symbols `p` which satisfy only the *congruence axiom*.
<pre><span class=hs-linenum>150: </span><span class='hs-keyword'>forall</span> <span class='hs-conid'>X</span><span class='hs-layout'>,</span> <span class='hs-conid'>Y</span><span class='hs-varop'>.</span> <span class='hs-keyword'>if</span> <span class='hs-layout'>(</span><span class='hs-conid'>X</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Y</span><span class='hs-layout'>)</span> <span class='hs-keyword'>then</span>  <span class='hs-varid'>p</span><span class='hs-layout'>(</span><span class='hs-conid'>X</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>p</span><span class='hs-layout'>(</span><span class='hs-conid'>Y</span><span class='hs-layout'>)</span>
</pre>

Happily, reasoning with such uninterpreted functions is quite decidable
(thanks to Ackermann, yes, *that* Ackermann) and actually rather efficient.
Thus, via SMT, LiquidHaskell happily verifies that `maxInt` indeed behaves
as advertised: the input types ensure that both `(p x)` and `(p y)` hold 
and hence that the returned value in either branch of `maxInt` satisfies 
the refinement  `{v:Int | p(v)}`, thereby ensuring the output type. 

By the same reasoning, we can define the `maximumInt` operator on lists:


<pre><span class=hs-linenum>163: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maximumInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span><span class='hs-keyword'>@-}</span>
<span class=hs-linenum>164: </span><a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; Bool&gt;.
[{VV : (GHC.Types.Int)&lt;p&gt; | true}]
-&gt; {VV : (GHC.Types.Int)&lt;p&gt; | true}</span><span class='hs-definition'>maximumInt</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>({VV : (GHC.Types.Int) | ((papp1 p VV))}
 -&gt; {VV : (GHC.Types.Int) | ((papp1 p VV))}
 -&gt; {VV : (GHC.Types.Int) | ((papp1 p VV))})
-&gt; {VV : (GHC.Types.Int) | ((papp1 p VV))}
-&gt; [{VV : (GHC.Types.Int) | ((papp1 p VV))}]
-&gt; {VV : (GHC.Types.Int) | ((papp1 p VV))}</span><span class='hs-varid'>foldr</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; Bool&gt;.
{VV : (GHC.Types.Int)&lt;p&gt; | true}
-&gt; {VV : (GHC.Types.Int)&lt;p&gt; | true}
-&gt; {VV : (GHC.Types.Int)&lt;p&gt; | true}</span><span class='hs-varid'>maxInt</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | ((papp1 p VV)) &amp;&amp; (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : (GHC.Types.Int) | ((papp1 p VV))}] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

Using Parametric Invariants
---------------------------

Its only useful to parametrize over invariants if there is some easy way 
to *instantiate* the parameters. 

Concretely, consider the function:


<pre><span class=hs-linenum>176: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maxEvens1</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| (Even v)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>177: </span><a class=annot href="#"><span class=annottext>[(GHC.Types.Int)] -&gt; {VV : (GHC.Types.Int) | ((VV mod 2) == 0)}</span><span class='hs-definition'>maxEvens1</span></a> <a class=annot href="#"><span class=annottext>[(GHC.Types.Int)]</span><span class='hs-varid'>xs</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; Bool&gt;.
[{VV : (GHC.Types.Int)&lt;p&gt; | true}]
-&gt; {VV : (GHC.Types.Int)&lt;p&gt; | true}</span><span class='hs-varid'>maximumInt</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : (GHC.Types.Int) | ((VV mod 2) == 0)}]&lt;\_ VV -&gt; ((VV mod 2) == 0)&gt; | (VV == xs'') &amp;&amp; ((len VV) == (1 + (len xs'))) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs''</span></a>
<span class=hs-linenum>178: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>179: </span>    <a class=annot href="#"><span class=annottext>{VV : [{VV : (GHC.Types.Int) | ((VV mod 2) == 0)}]&lt;\_ VV -&gt; ((VV mod 2) == 0)&gt; | ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs'</span></a>      <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>x</span> <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Int)] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Bool) | (((Prop VV)) &lt;=&gt; ((x mod 2) == 0))}</span><span class='hs-varid'>isEven</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>180: </span>    <a class=annot href="#"><span class=annottext>{VV : [{VV : (GHC.Types.Int) | ((VV mod 2) == 0)}]&lt;\_ VV -&gt; ((VV mod 2) == 0)&gt; | ((len VV) == (1 + (len xs')))}</span><span class='hs-varid'>xs''</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool&gt;.
y:{VV : (GHC.Types.Int) | ((VV mod 2) == 0)}
-&gt; ys:[{VV : (GHC.Types.Int)&lt;p y&gt; | ((VV mod 2) == 0)}]&lt;p&gt;
-&gt; {VV : [{VV : (GHC.Types.Int) | ((VV mod 2) == 0)}]&lt;p&gt; | ((len VV) == (1 + (len ys)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : (GHC.Types.Int) | ((VV mod 2) == 0)}]&lt;\_ VV -&gt; ((VV mod 2) == 0)&gt; | (VV == xs') &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs'</span></a>
</pre>

 where the function `isEven` is from the Language.Haskell.Liquid.Prelude library:
<pre><span class=hs-linenum>184: </span><span class='hs-comment'>{- isEven :: x:Int -&gt; {v:Bool | (Prop(v) &lt;=&gt; (Even x))} -}</span>
<span class=hs-linenum>185: </span><span class='hs-definition'>isEven</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>186: </span><span class='hs-definition'>isEven</span> <span class='hs-varid'>x</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>x</span> <span class='hs-varop'>`mod`</span> <span class='hs-num'>2</span> <span class='hs-varop'>==</span> <span class='hs-num'>0</span>
</pre>

where the predicate `Even` is defined as


<pre><span class=hs-linenum>192: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>Even</span> <span class='hs-conid'>X</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-conid'>X</span> <span class='hs-varid'>mod</span> <span class='hs-num'>2</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>

To verify that `maxEvens1` returns an even number, LiquidHaskell 

1. infers that the list `(0:xs')` has type `[{v:Int | (Even v)}]`, 
   that is, is a list of even numbers.

2. automatically instantiates the *refinement* parameter of 
   `maximumInt` with the concrete refinement `{\v -> (Even v)}` and so

3. concludes that the value returned by `maxEvens1` is indeed `Even`.

Parametric Invariants and Type Classes
--------------------------------------

Ok, lets be honest, the above is clearly quite contrived. After all,
wouldn't you write a *polymorphic* `max` function? And having done so,
we'd just get all the above goodness from old fashioned parametricity.

 That is to say, if we just wrote:
<pre><span class=hs-linenum>213: </span><span class='hs-definition'>max</span>     <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span><span class='hs-varop'>.</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>214: </span><span class='hs-definition'>max</span> <span class='hs-varid'>x</span> <span class='hs-varid'>y</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>if</span> <span class='hs-varid'>x</span> <span class='hs-varop'>&gt;</span> <span class='hs-varid'>y</span> <span class='hs-keyword'>then</span> <span class='hs-varid'>x</span> <span class='hs-keyword'>else</span> <span class='hs-varid'>y</span>
<span class=hs-linenum>215: </span>
<span class=hs-linenum>216: </span><span class='hs-definition'>maximum</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span><span class='hs-varop'>.</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>217: </span><span class='hs-definition'>maximum</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>foldr</span> <span class='hs-varid'>max</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span>
</pre>

then we could happily *instantiate* the `a` with `{v:Int | v > 0}` or
`{v:Int | (Even v)}` or whatever was needed at the call-site of `max`.
Sigh. Perhaps we are still pining for Hindley-Milner.

 Well, if this was an ML perhaps we could but in Haskell, the types would be 
<pre><span class=hs-linenum>225: </span><span class='hs-layout'>(</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span>     <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>226: </span><span class='hs-definition'>max</span>     <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>227: </span><span class='hs-definition'>maximum</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
</pre>

Our first temptation may be to furtively look over our shoulders, and
convinced no one was watching, just pretend that funny `(Ord a)` business
was not there, and quietly just treat `maximum` as `[a] -> a` and summon
parametricity.

That would be most unwise. We may get away with it with the harmless `Ord` but what of, say, `Num`. 

 Clearly a function 
<pre><span class=hs-linenum>238: </span><span class='hs-definition'>numCrunch</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Num</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
</pre>

is not going to necessarily return one of its inputs as an output. 
Thus, it is laughable to believe that `numCrunch` would, if given 
a list of  of even (or positive, negative, prime, RGB, ...) integers, 
return a even (or positive, negative, prime, RGB, ...) integer, since 
the function might add or subtract or multiply or do other unspeakable
things to the numbers in order to produce the output value.

And yet, typeclasses are everywhere. 

How could we possibly verify that


<pre><span class=hs-linenum>253: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maxEvens2</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| (Even v) }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>254: </span><a class=annot href="#"><span class=annottext>[(GHC.Types.Int)] -&gt; {VV : (GHC.Types.Int) | ((VV mod 2) == 0)}</span><span class='hs-definition'>maxEvens2</span></a> <a class=annot href="#"><span class=annottext>[(GHC.Types.Int)]</span><span class='hs-varid'>xs</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[{VV : (GHC.Types.Int) | ((VV mod 2) == 0)}]
-&gt; {VV : (GHC.Types.Int) | ((VV mod 2) == 0)}</span><span class='hs-varid'>maximumPoly</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : (GHC.Types.Int) | ((VV mod 2) == 0)}]&lt;\_ VV -&gt; ((VV mod 2) == 0)&gt; | (VV == xs'') &amp;&amp; ((len VV) == (1 + (len xs'))) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs''</span></a>
<span class=hs-linenum>255: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>256: </span>     <a class=annot href="#"><span class=annottext>{VV : [{VV : (GHC.Types.Int) | ((VV mod 2) == 0)}]&lt;\_ VV -&gt; ((VV mod 2) == 0)&gt; | ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs'</span></a>     <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>x</span> <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Int)] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Bool) | (((Prop VV)) &lt;=&gt; ((x mod 2) == 0))}</span><span class='hs-varid'>isEven</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>257: </span>     <a class=annot href="#"><span class=annottext>{VV : [{VV : (GHC.Types.Int) | ((VV mod 2) == 0)}]&lt;\_ VV -&gt; ((VV mod 2) == 0)&gt; | ((len VV) == (1 + (len xs')))}</span><span class='hs-varid'>xs''</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool&gt;.
y:{VV : (GHC.Types.Int) | ((VV mod 2) == 0)}
-&gt; ys:[{VV : (GHC.Types.Int)&lt;p y&gt; | ((VV mod 2) == 0)}]&lt;p&gt;
-&gt; {VV : [{VV : (GHC.Types.Int) | ((VV mod 2) == 0)}]&lt;p&gt; | ((len VV) == (1 + (len ys)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : (GHC.Types.Int) | ((VV mod 2) == 0)}]&lt;\_ VV -&gt; ((VV mod 2) == 0)&gt; | (VV == xs') &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs'</span></a>
</pre>

where the helpers were in the usual `Ord` style?


<pre><span class=hs-linenum>263: </span><span class='hs-definition'>maximumPoly</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>264: </span><a class=annot href="#"><span class=annottext>forall a &lt;p :: a-&gt; Bool&gt;.
(GHC.Classes.Ord a) =&gt;
[{VV : a&lt;p&gt; | true}] -&gt; {VV : a&lt;p&gt; | true}</span><span class='hs-definition'>maximumPoly</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>({VV : a | ((papp1 p VV))}
 -&gt; {VV : a | ((papp1 p VV))} -&gt; {VV : a | ((papp1 p VV))})
-&gt; {VV : a | ((papp1 p VV))}
-&gt; [{VV : a | ((papp1 p VV))}]
-&gt; {VV : a | ((papp1 p VV))}</span><span class='hs-varid'>foldr</span></a> <a class=annot href="#"><span class=annottext>{VV : a | ((papp1 p VV))}
-&gt; {VV : a | ((papp1 p VV))} -&gt; {VV : a | ((papp1 p VV))}</span><span class='hs-varid'>maxPoly</span></a> <a class=annot href="#"><span class=annottext>{VV : a | ((papp1 p VV)) &amp;&amp; (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | ((papp1 p VV))}] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>265: </span>
<span class=hs-linenum>266: </span><span class='hs-definition'>maxPoly</span>     <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>267: </span><a class=annot href="#"><span class=annottext>forall a &lt;p :: a-&gt; Bool&gt;.
(GHC.Classes.Ord a) =&gt;
{VV : a&lt;p&gt; | true} -&gt; {VV : a&lt;p&gt; | true} -&gt; {VV : a&lt;p&gt; | true}</span><span class='hs-definition'>maxPoly</span></a> <a class=annot href="#"><span class=annottext>{VV : a | ((papp1 p VV))}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : a | ((papp1 p VV))}</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>if</span> <a class=annot href="#"><span class=annottext>{VV : a | ((papp1 p VV)) &amp;&amp; (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:{VV : a | ((papp1 p VV))}
-&gt; y:{VV : a | ((papp1 p VV))}
-&gt; {VV : (GHC.Types.Bool) | (((Prop VV)) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : a | ((papp1 p VV)) &amp;&amp; (VV == y)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyword'>then</span> <a class=annot href="#"><span class=annottext>{VV : a | ((papp1 p VV)) &amp;&amp; (VV == y)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyword'>else</span> <a class=annot href="#"><span class=annottext>{VV : a | ((papp1 p VV)) &amp;&amp; (VV == x)}</span><span class='hs-varid'>x</span></a>
</pre>

The answer: abstract refinements.

First, via the same analysis as the monomorphic `Int` case, LiquidHaskell
establishes that


<pre><span class=hs-linenum>276: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maxPoly</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> 
<span class=hs-linenum>277: </span>                 <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>@-}</span>
</pre>

and hence, that


<pre><span class=hs-linenum>283: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maximumPoly</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> 
<span class=hs-linenum>284: </span>                     <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span>     <span class='hs-keyword'>@-}</span>
</pre>

Second, at the call-site for `maximumPoly` in `maxEvens2` LiquidHaskell 
instantiates the type variable `a` with `Int`, and the abstract refinement
parameter `p` with `{\v -> (Even v)}` after which, the verification proceeds 
as described earlier (for the `Int` case).

And So
------

If you've courageously slogged through to this point then you've learnt
that 

1. Sometimes, choosing the right type can be quite difficult! 

2. But fortunately, with *abstract refinements* we needn't choose, but 
   can write types that are parameterized over the actual concrete 
   invariants or refinements, which

3. Can be instantiated at the call-sites i.e. users of the functions.

We started with some really frivolous examples, but buckle your seatbelt 
and hold on tight, because we're going to see some rather nifty things that
this new technique makes possible, including induction, reasoning about
memoizing functions, and *ordering* and *sorting* data. Stay tuned.

[blog-dbz]:     /blog/2013/01/01/refinement-types-101.lhs/ 
[blog-len]:     /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/ 
[blog-vec]:     /blog/2013/03/04/bounding-vectors.lhs/
[blog-set]:     /blog/2013/03/26/talking/about/sets.lhs/
[blog-zip]:     /blog/2013/05/16/unique-zipper.lhs/
