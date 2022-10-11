---
layout: post
title: A Finer Filter
date: 2014-08-15 16:12
author: Ranjit Jhala
published: true
comments: true
tags:
   - abstract-refinements 
demo: filter.hs
---

This morning, I came across this [nice post](https://twitter.com/ertesx/status/500034598042996736) which describes how one can write a very expressive type for 
`filter` using [singletons](https://hackage.haskell.org/package/singletons).

Lets see how one might achieve this with [abstract refinements][absref].

<!-- more -->

<div class="hidden">


<pre><span class=hs-linenum>23: </span>
<span class=hs-linenum>24: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--short-names"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>25: </span>
<span class=hs-linenum>26: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Filter</span> <span class='hs-layout'>(</span><span class='hs-varid'>filter</span><span class='hs-layout'>)</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>27: </span>
<span class=hs-linenum>28: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>filter</span><span class='hs-layout'>)</span>
<span class=hs-linenum>29: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span><span class='hs-layout'>)</span>
<span class=hs-linenum>30: </span>
<span class=hs-linenum>31: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>filter</span><span class='hs-layout'>)</span>
<span class=hs-linenum>32: </span><span class='hs-definition'>isPos</span><span class='hs-layout'>,</span> <span class='hs-varid'>isEven</span><span class='hs-layout'>,</span> <span class='hs-varid'>isOdd</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Maybe</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>33: </span><span class='hs-definition'>filter</span><span class='hs-layout'>,</span> <span class='hs-varid'>filter3</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Maybe</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>34: </span>
<span class=hs-linenum>35: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>elts</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>36: </span>    <span class='hs-varid'>elts</span> <span class='hs-layout'>(</span><span class='hs-conid'>[]</span><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Set_emp</span> <span class='hs-varid'>v</span> <span class='hs-layout'>}</span>
<span class=hs-linenum>37: </span>    <span class='hs-varid'>elts</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Set_cup</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>elts</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-layout'>}</span>
<span class=hs-linenum>38: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>39: </span> 
</pre>

</div>

Goal
----

What we're after is a way to write a `filter` function such that:

 
<pre><span class=hs-linenum>50: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>getPoss</span>  <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Pos</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>51: </span><a class=annot href="#"><span class=annottext>x1:[{x7 : Int | false}]
-&gt; {x2 : [{x7 : Int | false}] | ((Set_sub (elts x2) (elts x1)))}</span><span class='hs-definition'>getPoss</span></a>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>({x10 : Int | false} -&gt; (Maybe {x10 : Int | false}))
-&gt; x3:[{x10 : Int | false}]
-&gt; {x2 : [{x10 : Int | false}] | ((Set_sub (elts x2) (elts x3)))}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>x1:Int
-&gt; (Maybe {x6 : Int | (x6 == x1) &amp;&amp; (x6 == (x1  :  int)) &amp;&amp; (x6 &gt; 0) &amp;&amp; (0 &lt; x6)})</span><span class='hs-varid'>isPos</span></a>
<span class=hs-linenum>52: </span>
<span class=hs-linenum>53: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>getEvens</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Even</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>54: </span><a class=annot href="#"><span class=annottext>x1:[{x7 : Int | false}]
-&gt; {x2 : [{x7 : Int | false}] | ((Set_sub (elts x2) (elts x1)))}</span><span class='hs-definition'>getEvens</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>({x10 : Int | false} -&gt; (Maybe {x10 : Int | false}))
-&gt; x3:[{x10 : Int | false}]
-&gt; {x2 : [{x10 : Int | false}] | ((Set_sub (elts x2) (elts x3)))}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>x1:Int
-&gt; (Maybe {x5 : Int | (x5 == x1) &amp;&amp; (x5 == (x1  :  int)) &amp;&amp; ((x5 mod 2) == 0)})</span><span class='hs-varid'>isEven</span></a>
<span class=hs-linenum>55: </span>
<span class=hs-linenum>56: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>getOdds</span>  <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Odd</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>57: </span><a class=annot href="#"><span class=annottext>x1:[{x7 : Int | false}]
-&gt; {x2 : [{x7 : Int | false}] | ((Set_sub (elts x2) (elts x1)))}</span><span class='hs-definition'>getOdds</span></a>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>({x10 : Int | false} -&gt; (Maybe {x10 : Int | false}))
-&gt; x3:[{x10 : Int | false}]
-&gt; {x2 : [{x10 : Int | false}] | ((Set_sub (elts x2) (elts x3)))}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>x1:Int
-&gt; (Maybe {x6 : Int | (x6 == x1) &amp;&amp; (x6 == (x1  :  int)) &amp;&amp; ((x6 mod 2) == 1) &amp;&amp; (x6 /= 0)})</span><span class='hs-varid'>isOdd</span></a>
</pre>

where `Pos`, `Even` and `Odd` are just subsets of `Int`:


<pre><span class=hs-linenum>63: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>Pos</span>  <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>|</span> <span class='hs-num'>0</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span>        <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>64: </span>
<span class=hs-linenum>65: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>Even</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varid'>mod</span> <span class='hs-num'>2</span> <span class='hs-varop'>==</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>66: </span>
<span class=hs-linenum>67: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>Odd</span>  <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varid'>mod</span> <span class='hs-num'>2</span> <span class='hs-varop'>/=</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

Take 1: Map, maybe?
-------------------

Bowing to the anti-boolean sentiment currently in the air, lets eschew 
the classical approach where the predicates (`isPos` etc.) return `True` 
or `False` and instead implement `filter` using a map.


<pre><span class=hs-linenum>78: </span><span class='hs-definition'>filter1</span>          <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Maybe</span> <span class='hs-varid'>b</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>b</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>79: </span>
<span class=hs-linenum>80: </span><a class=annot href="#"><span class=annottext>forall a b.
(a -&gt; (Maybe b))
-&gt; x3:[a] -&gt; {VV : [b] | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x3))}</span><span class='hs-definition'>filter1</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (Maybe b)</span><span class='hs-varid'>f</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a &lt;p :: a a -&gt; Prop&gt;.
{x5 : [a]&lt;\x6 VV -&gt; p x6&gt; | (((null x5)) &lt;=&gt; true) &amp;&amp; ((Set_emp (listElts x5))) &amp;&amp; ((Set_emp (elts x5))) &amp;&amp; ((len x5) == 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>81: </span><span class='hs-definition'>filter1</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>case</span> <a class=annot href="#"><span class=annottext>a -&gt; (Maybe b)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <span class='hs-keyword'>of</span>
<span class=hs-linenum>82: </span>                     <span class='hs-conid'>Just</span> <span class='hs-varid'>y</span>  <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>x1:a
-&gt; x2:[a]
-&gt; {x5 : [a] | (((null x5)) &lt;=&gt; false) &amp;&amp; ((listElts x5) == (Set_cup (Set_sng x1) (listElts x2))) &amp;&amp; ((len x5) == (1 + (len x2))) &amp;&amp; ((elts x5) == (Set_cup (Set_sng x1) (elts x2)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a b.
(a -&gt; (Maybe b))
-&gt; x3:[a] -&gt; {VV : [b] | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x3))}</span><span class='hs-varid'>filter1</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (Maybe b)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x3 : [a] | (x3 == xs) &amp;&amp; ((len x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> 
<span class=hs-linenum>83: </span>                     <span class='hs-conid'>Nothing</span> <span class='hs-keyglyph'>-&gt;</span>     <a class=annot href="#"><span class=annottext>forall a b.
(a -&gt; (Maybe b))
-&gt; x3:[a] -&gt; {VV : [b] | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x3))}</span><span class='hs-varid'>filter1</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (Maybe b)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x3 : [a] | (x3 == xs) &amp;&amp; ((len x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

To complete the picture, we need just define the predicates as
functions returning a `Maybe`:


<pre><span class=hs-linenum>90: </span><span class='hs-comment'>{- isPos          :: Int -&gt; Maybe Pos  @-}</span>
<span class=hs-linenum>91: </span><a class=annot href="#"><span class=annottext>x:Int
-&gt; (Maybe {VV : Int | (VV == x) &amp;&amp; (VV == (x  :  int)) &amp;&amp; (VV &gt; 0) &amp;&amp; (0 &lt; VV)})</span><span class='hs-definition'>isPos</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>92: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 &gt; x2))}</span><span class='hs-varop'>&gt;</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a>          <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x13 : Int | (x13 == x) &amp;&amp; (x13 == (x  :  int)) &amp;&amp; (x13 &gt; 0) &amp;&amp; (0 &lt; x13)}
-&gt; {x3 : (Maybe {x13 : Int | (x13 == x) &amp;&amp; (x13 == (x  :  int)) &amp;&amp; (x13 &gt; 0) &amp;&amp; (0 &lt; x13)}) | (((isJust x3)) &lt;=&gt; true) &amp;&amp; ((fromJust x3) == x1)}</span><span class='hs-conid'>Just</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == x)}</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>93: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : (Maybe {x3 : Int | false}) | (((isJust x2)) &lt;=&gt; false)}</span><span class='hs-conid'>Nothing</span></a>
<span class=hs-linenum>94: </span>
<span class=hs-linenum>95: </span><span class='hs-comment'>{- isEven         :: Int -&gt; Maybe Even @-}</span>
<span class=hs-linenum>96: </span><a class=annot href="#"><span class=annottext>x:Int
-&gt; (Maybe {VV : Int | (VV == x) &amp;&amp; (VV == (x  :  int)) &amp;&amp; ((VV mod 2) == 0)})</span><span class='hs-definition'>isEven</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>97: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:Int
-&gt; x2:Int
-&gt; {x6 : Int | (((0 &lt;= x1) &amp;&amp; (0 &lt; x2)) =&gt; ((0 &lt;= x6) &amp;&amp; (x6 &lt; x2))) &amp;&amp; (x6 == (x1 mod x2))}</span><span class='hs-varop'>`mod`</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (2  :  int))}</span><span class='hs-num'>2</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 == x2))}</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x11 : Int | (x11 == x) &amp;&amp; (x11 == (x  :  int)) &amp;&amp; ((x11 mod 2) == 0)}
-&gt; {x3 : (Maybe {x11 : Int | (x11 == x) &amp;&amp; (x11 == (x  :  int)) &amp;&amp; ((x11 mod 2) == 0)}) | (((isJust x3)) &lt;=&gt; true) &amp;&amp; ((fromJust x3) == x1)}</span><span class='hs-conid'>Just</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == x)}</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>98: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : (Maybe {x3 : Int | false}) | (((isJust x2)) &lt;=&gt; false)}</span><span class='hs-conid'>Nothing</span></a>
<span class=hs-linenum>99: </span>
<span class=hs-linenum>100: </span><span class='hs-comment'>{- isOdd          :: Int -&gt; Maybe Odd  @-}</span>
<span class=hs-linenum>101: </span><a class=annot href="#"><span class=annottext>x:Int
-&gt; (Maybe {VV : Int | (VV == x) &amp;&amp; (VV == (x  :  int)) &amp;&amp; ((VV mod 2) == 1) &amp;&amp; (VV /= 0)})</span><span class='hs-definition'>isOdd</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>102: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:Int
-&gt; x2:Int
-&gt; {x6 : Int | (((0 &lt;= x1) &amp;&amp; (0 &lt; x2)) =&gt; ((0 &lt;= x6) &amp;&amp; (x6 &lt; x2))) &amp;&amp; (x6 == (x1 mod x2))}</span><span class='hs-varop'>`mod`</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (2  :  int))}</span><span class='hs-num'>2</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 /= x2))}</span><span class='hs-varop'>/=</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x13 : Int | (x13 == x) &amp;&amp; (x13 == (x  :  int)) &amp;&amp; ((x13 mod 2) == 1) &amp;&amp; (x13 /= 0)}
-&gt; {x3 : (Maybe {x13 : Int | (x13 == x) &amp;&amp; (x13 == (x  :  int)) &amp;&amp; ((x13 mod 2) == 1) &amp;&amp; (x13 /= 0)}) | (((isJust x3)) &lt;=&gt; true) &amp;&amp; ((fromJust x3) == x1)}</span><span class='hs-conid'>Just</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == x)}</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>103: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : (Maybe {x3 : Int | false}) | (((isJust x2)) &lt;=&gt; false)}</span><span class='hs-conid'>Nothing</span></a>
</pre>

and now, we can achieve our goal!


<pre><span class=hs-linenum>109: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>getPoss1</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Pos</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>110: </span><a class=annot href="#"><span class=annottext>[Int] -&gt; [{v : Int | (0 &lt; v)}]</span><span class='hs-definition'>getPoss1</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(Int -&gt; (Maybe {x14 : Int | (x14 &gt; 0) &amp;&amp; (0 &lt; x14)}))
-&gt; x3:[Int]
-&gt; {x3 : [{x14 : Int | (x14 &gt; 0) &amp;&amp; (0 &lt; x14)}] | ((len x3) &gt;= 0) &amp;&amp; ((len x3) &lt;= (len x3))}</span><span class='hs-varid'>filter1</span></a> <a class=annot href="#"><span class=annottext>x1:Int
-&gt; (Maybe {x6 : Int | (x6 == x1) &amp;&amp; (x6 == (x1  :  int)) &amp;&amp; (x6 &gt; 0) &amp;&amp; (0 &lt; x6)})</span><span class='hs-varid'>isPos</span></a>
<span class=hs-linenum>111: </span>
<span class=hs-linenum>112: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>getEvens1</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Even</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>113: </span><a class=annot href="#"><span class=annottext>[Int] -&gt; [{v : Int | ((v mod 2) == 0)}]</span><span class='hs-definition'>getEvens1</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(Int -&gt; (Maybe {x12 : Int | ((x12 mod 2) == 0)}))
-&gt; x3:[Int]
-&gt; {x3 : [{x12 : Int | ((x12 mod 2) == 0)}] | ((len x3) &gt;= 0) &amp;&amp; ((len x3) &lt;= (len x3))}</span><span class='hs-varid'>filter1</span></a> <a class=annot href="#"><span class=annottext>x1:Int
-&gt; (Maybe {x5 : Int | (x5 == x1) &amp;&amp; (x5 == (x1  :  int)) &amp;&amp; ((x5 mod 2) == 0)})</span><span class='hs-varid'>isEven</span></a>
<span class=hs-linenum>114: </span>
<span class=hs-linenum>115: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>getOdds1</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Odd</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>116: </span><a class=annot href="#"><span class=annottext>[Int] -&gt; [{v : Int | ((v mod 2) == 1)}]</span><span class='hs-definition'>getOdds1</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(Int -&gt; (Maybe {x14 : Int | ((x14 mod 2) == 1) &amp;&amp; (x14 /= 0)}))
-&gt; x3:[Int]
-&gt; {x3 : [{x14 : Int | ((x14 mod 2) == 1) &amp;&amp; (x14 /= 0)}] | ((len x3) &gt;= 0) &amp;&amp; ((len x3) &lt;= (len x3))}</span><span class='hs-varid'>filter1</span></a> <a class=annot href="#"><span class=annottext>x1:Int
-&gt; (Maybe {x6 : Int | (x6 == x1) &amp;&amp; (x6 == (x1  :  int)) &amp;&amp; ((x6 mod 2) == 1) &amp;&amp; (x6 /= 0)})</span><span class='hs-varid'>isOdd</span></a>
</pre>

**The Subset Guarantee**

Well that was easy! Or was it?

I fear we've *cheated* a little bit.

One of the nice things about the *classical* `filter` is that by eyeballing
the signature:


<pre><span class=hs-linenum>129: </span><span class='hs-definition'>filter</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
</pre>

we are guaranteed, via parametricity, that the output list's elements are
a *subset of* the input list's elements. The signature for our new-fangled


<pre><span class=hs-linenum>136: </span><span class='hs-definition'>filter1</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Maybe</span> <span class='hs-varid'>b</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>b</span><span class='hs-keyglyph'>]</span>
</pre>

yields no such guarantee!

In this case, things work out, because in each case, LiquidHaskell *instantiates*
the type variables `a` and `b` in the signature of `filter1` suitably:

* In `getPoss ` LH instantiates `a := Int` and `b := Pos`
* In `getEvens` LH instantiates `a := Int` and `b := Even`
* In `getOdds ` LH instantiates `a := Int` and `b := Odd`

(Hover over the different instances of `filter1` above to confirm this.)

But in general, we'd rather *not* lose the nice "subset" guarantee that the
classical `filter` provides.


Take 2: One Type Variable
-------------------------

Easy enough! Why do we need *two* type variables anyway?


<pre><span class=hs-linenum>160: </span><span class='hs-definition'>filter2</span>          <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Maybe</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>161: </span>
<span class=hs-linenum>162: </span><a class=annot href="#"><span class=annottext>forall a.
(x2:a -&gt; (Maybe {VV : a | (VV == x2)}))
-&gt; x3:[a]
-&gt; {VV : [a] | ((Set_sub (elts VV) (elts x3))) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x3))}</span><span class='hs-definition'>filter2</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; (Maybe {VV : a | (VV == x1)})</span><span class='hs-varid'>f</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a &lt;p :: a a -&gt; Prop&gt;.
{x5 : [a]&lt;\x6 VV -&gt; p x6&gt; | (((null x5)) &lt;=&gt; true) &amp;&amp; ((Set_emp (listElts x5))) &amp;&amp; ((Set_emp (elts x5))) &amp;&amp; ((len x5) == 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>163: </span><span class='hs-definition'>filter2</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>case</span> <a class=annot href="#"><span class=annottext>x1:a -&gt; (Maybe {VV : a | (VV == x1)})</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <span class='hs-keyword'>of</span>
<span class=hs-linenum>164: </span>                     <span class='hs-conid'>Just</span> <span class='hs-varid'>y</span>  <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y) &amp;&amp; (VV == x)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>x1:a
-&gt; x2:[a]
-&gt; {x5 : [a] | (((null x5)) &lt;=&gt; false) &amp;&amp; ((listElts x5) == (Set_cup (Set_sng x1) (listElts x2))) &amp;&amp; ((len x5) == (1 + (len x2))) &amp;&amp; ((elts x5) == (Set_cup (Set_sng x1) (elts x2)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
(x2:a -&gt; (Maybe {VV : a | (VV == x2)}))
-&gt; x3:[a]
-&gt; {VV : [a] | ((Set_sub (elts VV) (elts x3))) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x3))}</span><span class='hs-varid'>filter2</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; (Maybe {VV : a | (VV == x1)})</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x3 : [a] | (x3 == xs) &amp;&amp; ((len x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> 
<span class=hs-linenum>165: </span>                     <span class='hs-conid'>Nothing</span> <span class='hs-keyglyph'>-&gt;</span>     <a class=annot href="#"><span class=annottext>forall a.
(x2:a -&gt; (Maybe {VV : a | (VV == x2)}))
-&gt; x3:[a]
-&gt; {VV : [a] | ((Set_sub (elts VV) (elts x3))) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x3))}</span><span class='hs-varid'>filter2</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; (Maybe {VV : a | (VV == x1)})</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x3 : [a] | (x3 == xs) &amp;&amp; ((len x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

There! Now the `f` is forced to take or leave its input `x`, 
and so we can breathe easy knowing that `filter2` returns a 
subset of its inputs.

But...


<pre><span class=hs-linenum>175: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>getPoss2</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Pos</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>176: </span><a class=annot href="#"><span class=annottext>[Int] -&gt; [{v : Int | (0 &lt; v)}]</span><span class='hs-definition'>getPoss2</span></a>     <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>(x2:Int -&gt; (Maybe {x13 : Int | (x13 == x2)}))
-&gt; x3:[Int]
-&gt; {x4 : [Int] | ((Set_sub (elts x4) (elts x3))) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((len x4) &lt;= (len x3))}</span><span class='hs-varid'>filter2</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>x1:Int
-&gt; (Maybe {x6 : Int | (x6 == x1) &amp;&amp; (x6 == (x1  :  int)) &amp;&amp; (x6 &gt; 0) &amp;&amp; (0 &lt; x6)})</span><span class='hs-varid'>isPos</span></a></span>
<span class=hs-linenum>177: </span>
<span class=hs-linenum>178: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>getEvens2</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Even</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>179: </span><a class=annot href="#"><span class=annottext>[Int] -&gt; [{v : Int | ((v mod 2) == 0)}]</span><span class='hs-definition'>getEvens2</span></a>    <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>(x2:Int -&gt; (Maybe {x13 : Int | (x13 == x2)}))
-&gt; x3:[Int]
-&gt; {x4 : [Int] | ((Set_sub (elts x4) (elts x3))) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((len x4) &lt;= (len x3))}</span><span class='hs-varid'>filter2</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>x1:Int
-&gt; (Maybe {x5 : Int | (x5 == x1) &amp;&amp; (x5 == (x1  :  int)) &amp;&amp; ((x5 mod 2) == 0)})</span><span class='hs-varid'>isEven</span></a></span>
<span class=hs-linenum>180: </span>
<span class=hs-linenum>181: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>getOdds2</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Odd</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>182: </span><a class=annot href="#"><span class=annottext>[Int] -&gt; [{v : Int | ((v mod 2) == 1)}]</span><span class='hs-definition'>getOdds2</span></a>     <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>(x2:Int -&gt; (Maybe {x13 : Int | (x13 == x2)}))
-&gt; x3:[Int]
-&gt; {x4 : [Int] | ((Set_sub (elts x4) (elts x3))) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((len x4) &lt;= (len x3))}</span><span class='hs-varid'>filter2</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>x1:Int
-&gt; (Maybe {x6 : Int | (x6 == x1) &amp;&amp; (x6 == (x1  :  int)) &amp;&amp; ((x6 mod 2) == 1) &amp;&amp; (x6 /= 0)})</span><span class='hs-varid'>isOdd</span></a></span>
</pre>

Yikes, LH is not impressed -- the red highlight indicates that LH is not
convinced that the functions have the specified types.

Perhaps you know why already?

Since we used **the same** type variable `a` for *both* the 
input *and* output, LH must instantiate `a` with a type that 
matches *both* the input and output, i.e. is a *super-type*
of both, which is simply `Int` in all the cases. 

Consequently, we get the errors above -- "expected `Pos` but got `Int`".

Take 3: Add Abstract Refinement
-------------------------------

What we need is a generic way of specifying that the 
output of the predicate is not just an `a` but an `a` 
that *also* enjoys whatever property we are filtering for. 

This sounds like a job for [abstract refinements][absref] which
let us parameterize a signature over its refinements:


<pre><span class=hs-linenum>208: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>filter3</span>      <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span>
<span class=hs-linenum>209: </span>                      <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Maybe</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>210: </span><a class=annot href="#"><span class=annottext>forall a &lt;p :: a -&gt; Prop&gt;.
(a -&gt; (Maybe {VV : a&lt;p&gt; | true})) -&gt; [a] -&gt; [{VV : a&lt;p&gt; | true}]</span><span class='hs-definition'>filter3</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (Maybe {VV : a | ((papp1 p VV))})</span><span class='hs-varid'>f</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a &lt;p :: a a -&gt; Prop&gt;.
{x5 : [a]&lt;\x6 VV -&gt; p x6&gt; | (((null x5)) &lt;=&gt; true) &amp;&amp; ((Set_emp (listElts x5))) &amp;&amp; ((Set_emp (elts x5))) &amp;&amp; ((len x5) == 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>211: </span><span class='hs-definition'>filter3</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>case</span> <a class=annot href="#"><span class=annottext>a -&gt; (Maybe {VV : a | ((papp1 p VV))})</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <span class='hs-keyword'>of</span>
<span class=hs-linenum>212: </span>                     <span class='hs-conid'>Just</span> <span class='hs-varid'>x'</span>  <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{VV : a | ((papp1 p VV)) &amp;&amp; (VV == x')}</span><span class='hs-varid'>x'</span></a> <a class=annot href="#"><span class=annottext>x1:{VV : a | ((papp1 p VV))}
-&gt; x2:[{VV : a | ((papp1 p VV))}]&lt;\_ VV -&gt; ((papp1 p VV))&gt;
-&gt; {x5 : [{VV : a | ((papp1 p VV))}]&lt;\_ VV -&gt; ((papp1 p VV))&gt; | (((null x5)) &lt;=&gt; false) &amp;&amp; ((listElts x5) == (Set_cup (Set_sng x1) (listElts x2))) &amp;&amp; ((len x5) == (1 + (len x2))) &amp;&amp; ((elts x5) == (Set_cup (Set_sng x1) (elts x2)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a &lt;p :: a -&gt; Prop&gt;.
(a -&gt; (Maybe {VV : a&lt;p&gt; | true})) -&gt; [a] -&gt; [{VV : a&lt;p&gt; | true}]</span><span class='hs-varid'>filter3</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (Maybe {VV : a | ((papp1 p VV))})</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x3 : [a] | (x3 == xs) &amp;&amp; ((len x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> 
<span class=hs-linenum>213: </span>                     <span class='hs-conid'>Nothing</span> <span class='hs-keyglyph'>-&gt;</span>       <a class=annot href="#"><span class=annottext>forall a &lt;p :: a -&gt; Prop&gt;.
(a -&gt; (Maybe {VV : a&lt;p&gt; | true})) -&gt; [a] -&gt; [{VV : a&lt;p&gt; | true}]</span><span class='hs-varid'>filter3</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (Maybe {VV : a | ((papp1 p VV))})</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x3 : [a] | (x3 == xs) &amp;&amp; ((len x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

 Now, we've **decoupled** the filter-property from the type variable `a`.

The input still is a mere `a`, but the output is an `a` with bells on,
specifically, which satisfies the (abstract) refinement `p`.

Voila!


<pre><span class=hs-linenum>224: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>getPoss3</span>  <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Pos</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>225: </span><a class=annot href="#"><span class=annottext>[Int] -&gt; [{v : Int | (0 &lt; v)}]</span><span class='hs-definition'>getPoss3</span></a>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(Int -&gt; (Maybe {x13 : Int | (x13 &gt; 0) &amp;&amp; (0 &lt; x13)}))
-&gt; [Int] -&gt; [{x13 : Int | (x13 &gt; 0) &amp;&amp; (0 &lt; x13)}]</span><span class='hs-varid'>filter3</span></a> <a class=annot href="#"><span class=annottext>x1:Int
-&gt; (Maybe {x6 : Int | (x6 == x1) &amp;&amp; (x6 == (x1  :  int)) &amp;&amp; (x6 &gt; 0) &amp;&amp; (0 &lt; x6)})</span><span class='hs-varid'>isPos</span></a>
<span class=hs-linenum>226: </span>
<span class=hs-linenum>227: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>getEvens3</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Even</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>228: </span><a class=annot href="#"><span class=annottext>[Int] -&gt; [{v : Int | ((v mod 2) == 0)}]</span><span class='hs-definition'>getEvens3</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(Int -&gt; (Maybe {x11 : Int | ((x11 mod 2) == 0)}))
-&gt; [Int] -&gt; [{x11 : Int | ((x11 mod 2) == 0)}]</span><span class='hs-varid'>filter3</span></a> <a class=annot href="#"><span class=annottext>x1:Int
-&gt; (Maybe {x5 : Int | (x5 == x1) &amp;&amp; (x5 == (x1  :  int)) &amp;&amp; ((x5 mod 2) == 0)})</span><span class='hs-varid'>isEven</span></a>
<span class=hs-linenum>229: </span>
<span class=hs-linenum>230: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>getOdds3</span>  <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Odd</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>231: </span><a class=annot href="#"><span class=annottext>[Int] -&gt; [{v : Int | ((v mod 2) == 1)}]</span><span class='hs-definition'>getOdds3</span></a>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(Int -&gt; (Maybe {x13 : Int | ((x13 mod 2) == 1) &amp;&amp; (x13 /= 0)}))
-&gt; [Int] -&gt; [{x13 : Int | ((x13 mod 2) == 1) &amp;&amp; (x13 /= 0)}]</span><span class='hs-varid'>filter3</span></a> <a class=annot href="#"><span class=annottext>x1:Int
-&gt; (Maybe {x6 : Int | (x6 == x1) &amp;&amp; (x6 == (x1  :  int)) &amp;&amp; ((x6 mod 2) == 1) &amp;&amp; (x6 /= 0)})</span><span class='hs-varid'>isOdd</span></a>
</pre>

Now, LH happily accepts each of the above.

At each *use* of `filter` LH separately *instantiates* the `a` and
the `p`. In each case, the `a` is just `Int` but the `p` is instantiated as:

+ In `getPoss ` LH instantiates `p := \v -> 0 <= v`
+ In `getEvens` LH instantiates `p := \v -> v mod 2 == 0`
+ In `getOdds ` LH instantiates `p := \v -> v mod 2 /= 0`

That is, in each case, LH instantiates `p` with the refinement that describes
the output type we are looking for.

**Edit:** At this point, I was ready to go to bed, and so happily 
declared victory and turned in. The next morning, [mypetclone](http://www.reddit.com/r/haskell/comments/2dozs5/liquidhaskell_a_finer_filter/cjrrx3y)
graciously pointed out my folly: the signature for `filter3` makes no guarantees
about the subset property. In fact, 


<pre><span class=hs-linenum>252: </span><a class=annot href="#"><span class=annottext>[Integer] -&gt; [Integer]</span><span class='hs-definition'>doubles</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(Integer -&gt; (Maybe Integer)) -&gt; [Integer] -&gt; [Integer]</span><span class='hs-varid'>filter3</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>Integer -&gt; (Maybe Integer)</span><span class='hs-keyglyph'>\</span></a><a class=annot href="#"><span class=annottext>Integer</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>x1:Integer
-&gt; {x3 : (Maybe Integer) | (((isJust x3)) &lt;=&gt; true) &amp;&amp; ((fromJust x3) == x1)}</span><span class='hs-conid'>Just</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x2 : Integer | (x2 == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:Integer -&gt; x2:Integer -&gt; {x4 : Integer | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{x2 : Integer | (x2 == x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span> 
</pre>

typechecks just fine, while `doubles` clearly violates the subset property. 

Take 4: 
-------

I suppose the moral is that it may be tricky -- for me at least! -- to read more into
a type than what it *actually says*. Fortunately, with refinements, our types can say
quite a lot.

In particular, lets make the subset property explicit, by

1. Requiring the predicate return its input (or nothing), and,
2. Ensuring  the output is indeed a subset of the inputs.


<pre><span class=hs-linenum>270: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>filter</span>      <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span>
<span class=hs-linenum>271: </span>                       <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Maybe</span> <span class='hs-keyword'>{v:</span><span class='hs-definition'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>| v = x}</span><span class='hs-layout'>)</span>
<span class=hs-linenum>272: </span>                    <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>273: </span>                    <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| Set_sub (elts v) (elts xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>274: </span>
<span class=hs-linenum>275: </span><a class=annot href="#"><span class=annottext>forall a &lt;p :: a -&gt; Prop&gt;.
(x2:a -&gt; (Maybe {VV : a&lt;p&gt; | (VV == x2)}))
-&gt; x3:[a]
-&gt; {v : [{VV : a&lt;p&gt; | true}] | ((Set_sub (elts v) (elts x3)))}</span><span class='hs-definition'>filter</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; (Maybe {VV : a | ((papp1 p VV)) &amp;&amp; (VV == x1)})</span><span class='hs-varid'>f</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a &lt;p :: a a -&gt; Prop&gt;.
{x5 : [a]&lt;\x6 VV -&gt; p x6&gt; | (((null x5)) &lt;=&gt; true) &amp;&amp; ((Set_emp (listElts x5))) &amp;&amp; ((Set_emp (elts x5))) &amp;&amp; ((len x5) == 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>276: </span><span class='hs-definition'>filter</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>case</span> <a class=annot href="#"><span class=annottext>x1:a -&gt; (Maybe {VV : a | ((papp1 p VV)) &amp;&amp; (VV == x1)})</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <span class='hs-keyword'>of</span>
<span class=hs-linenum>277: </span>                    <span class='hs-conid'>Just</span> <span class='hs-varid'>x'</span>  <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{VV : a | ((papp1 p VV)) &amp;&amp; (VV == x) &amp;&amp; (VV == x')}</span><span class='hs-varid'>x'</span></a> <a class=annot href="#"><span class=annottext>x1:{VV : a | ((papp1 p VV))}
-&gt; x2:[{VV : a | ((papp1 p VV))}]&lt;\_ VV -&gt; ((papp1 p VV))&gt;
-&gt; {x5 : [{VV : a | ((papp1 p VV))}]&lt;\_ VV -&gt; ((papp1 p VV))&gt; | (((null x5)) &lt;=&gt; false) &amp;&amp; ((listElts x5) == (Set_cup (Set_sng x1) (listElts x2))) &amp;&amp; ((len x5) == (1 + (len x2))) &amp;&amp; ((elts x5) == (Set_cup (Set_sng x1) (elts x2)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a &lt;p :: a -&gt; Prop&gt;.
(x2:a -&gt; (Maybe {VV : a&lt;p&gt; | (VV == x2)}))
-&gt; x3:[a]
-&gt; {v : [{VV : a&lt;p&gt; | true}] | ((Set_sub (elts v) (elts x3)))}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; (Maybe {VV : a | ((papp1 p VV)) &amp;&amp; (VV == x1)})</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x3 : [a] | (x3 == xs) &amp;&amp; ((len x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> 
<span class=hs-linenum>278: </span>                    <span class='hs-conid'>Nothing</span> <span class='hs-keyglyph'>-&gt;</span>       <a class=annot href="#"><span class=annottext>forall a &lt;p :: a -&gt; Prop&gt;.
(x2:a -&gt; (Maybe {VV : a&lt;p&gt; | (VV == x2)}))
-&gt; x3:[a]
-&gt; {v : [{VV : a&lt;p&gt; | true}] | ((Set_sub (elts v) (elts x3)))}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; (Maybe {VV : a | ((papp1 p VV)) &amp;&amp; (VV == x1)})</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x3 : [a] | (x3 == xs) &amp;&amp; ((len x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

where `elts` describes the [set of elements in a list][sets].

**Note:** The *implementation* of each of the above `filter` functions are
the same; they only differ in their type *specification*.

Conclusion
----------

And so, using abstract refinements, we've written a `filter` whose signature guarantees:

* The outputs must be a *subset* of the inputs, and
* The outputs indeed satisfy the property being filtered for.

Another thing that I've learnt from this exercise, is that the old 
school `Boolean` approach has its merits. Take a look at the clever 
"latent predicates" technique of [Tobin-Hochstadt and Felleisen][racket]
or this lovely new paper by [Kaki and Jagannathan][catalyst] which
shows how refinements can be further generalized to make Boolean filters fine.

[sets]:   /blog/2013/03/26/talking-about-sets.lhs/ 
[absref]:   /blog/2013/06/03/abstracting-over-refinements.lhs/ 
[racket]:   http://www.ccs.neu.edu/racket/pubs/popl08-thf.pdf
[catalyst]: http://gowthamk.github.io/docs/icfp77-kaki.pdf
