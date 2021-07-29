---
layout: post
title: Measures and Case Splitting
date: 2018-02-23
comments: true
author: Niki Vazou
published: true
tags: measures, advanced
demo: MeasuresAndCaseSplitting.hs
---

Liquid Haskell has a flag called `--no-case-expand`
which can make verification of your code much faster, 
especially when your code is using ADTs with many alternatives.
This flag says relax precision to get fast verification, 
thus may lead to rejecting safe code. 

In this post, I explain how `--no-case-expand` 
works using a trivial example!

(Click here to [demo][demo])

<!-- more -->


<div class="hidden">

<pre><span class=hs-linenum>28: </span>
<span class=hs-linenum>29: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>MeasuresAndCaseSplitting</span> <span class='hs-keyword'>where</span>
</pre>
</div>


Measures
---------

Let's define a simple data type with three alternatives 


<pre><span class=hs-linenum>40: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>ABC</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>A</span> <span class='hs-keyglyph'>|</span> <span class='hs-conid'>B</span> <span class='hs-keyglyph'>|</span> <span class='hs-conid'>C</span> 
</pre>

and a measure that turns `ABD` into an integer


<pre><span class=hs-linenum>46: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>toInt</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>47: </span><span class='hs-definition'>toInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>ABC</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> 
<span class=hs-linenum>48: </span><a class=annot href="#"><span class=annottext>x1:MeasuresAndCaseSplitting.ABC -&gt; {VV : GHC.Types.Int | VV == MeasuresAndCaseSplitting.toInt x1}</span><span class='hs-definition'>toInt</span></a> <span class='hs-conid'>A</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> 
<span class=hs-linenum>49: </span><span class='hs-definition'>toInt</span> <span class='hs-conid'>B</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>2</span>
<span class=hs-linenum>50: </span><span class='hs-definition'>toInt</span> <span class='hs-conid'>C</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>3</span> 
</pre>

Though obvious to us, Liquid Haskell will fail to check 
that `toInt` of any `ABC` argument
gives back a natural number. 
Or, the following call leads to a refinement type error. 


<pre><span class=hs-linenum>59: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>unsafe</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>ABC</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{o:</span><span class='hs-conid'>()</span> <span class='hs-keyword'>| 0 &lt;= toInt x }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>60: </span><span class='hs-keyword'>unsafe</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>ABC</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span> 
<span class=hs-linenum>61: </span><span class=hs-error><a class=annot href="#"><span class=annottext>x1:MeasuresAndCaseSplitting.ABC -&gt; {o : () | 0 &lt;= MeasuresAndCaseSplitting.toInt x1}</span><span class='hs-keyword'>unsafe</span></a></span> <a class=annot href="#"><span class=annottext>MeasuresAndCaseSplitting.ABC</span><span class='hs-varid'>x</span></a>   <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span>
</pre>

Why? 
By turning `toInt` into a measure, Liquid Haskell
gives precise information to each data constructor of `ABC`. 
Thus it knows that `toInt` or `A`, `B`, and `C`
is respectively `1`, `2`, and `3`, by *automatically* 
generating the following types: 


<pre><span class=hs-linenum>72: </span><span class='hs-conid'>A</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>ABC</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>toInt</span> <span class='hs-varid'>v</span> <span class='hs-varop'>==</span> <span class='hs-num'>1</span> <span class='hs-layout'>}</span>
<span class=hs-linenum>73: </span><span class='hs-conid'>B</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>ABC</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>toInt</span> <span class='hs-varid'>v</span> <span class='hs-varop'>==</span> <span class='hs-num'>2</span> <span class='hs-layout'>}</span>
<span class=hs-linenum>74: </span><span class='hs-conid'>C</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>ABC</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>toInt</span> <span class='hs-varid'>v</span> <span class='hs-varop'>==</span> <span class='hs-num'>3</span> <span class='hs-layout'>}</span>
</pre>

Thus, to get the `toInt` information one need to 
explicitly perform case analysis on an `ABC` argument. 
The following code is safe


<pre><span class=hs-linenum>82: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>safe</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>ABC</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{o:</span><span class='hs-conid'>()</span> <span class='hs-keyword'>| 0 &lt;= toInt x}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>83: </span><span class='hs-keyword'>safe</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>ABC</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>84: </span><a class=annot href="#"><span class=annottext>x1:MeasuresAndCaseSplitting.ABC -&gt; {o : () | 0 &lt;= MeasuresAndCaseSplitting.toInt x1}</span><span class='hs-keyword'>safe</span></a> <span class='hs-conid'>A</span>   <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span> 
<span class=hs-linenum>85: </span><span class='hs-keyword'>safe</span> <span class='hs-conid'>B</span>   <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span> 
<span class=hs-linenum>86: </span><span class='hs-keyword'>safe</span> <span class='hs-conid'>C</span>   <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span> 
</pre>

Liquid Haskell type check the above code because 
in the first case the body is checked under the assumption 
that the argument, call it `x`, is an `A`. 
Under this assumption, `toInt x` is indeed non negative. 
Yet, this is the case for the rest two alternatives, 
where `x` is either `B` or `C`. 
So, `0 <= toInt x` holds for all the alternatives, 
because case analysis on `x` automatically reasons about the 
value of the measure `toInt`. 


Now, what if I match the argument `x` only with `A`
and provide a default body for the rest?


<pre><span class=hs-linenum>104: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>safeBut</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>ABC</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{o:</span><span class='hs-conid'>()</span> <span class='hs-keyword'>| 0 &lt;= toInt x}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>105: </span><span class='hs-definition'>safeBut</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>ABC</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>106: </span><a class=annot href="#"><span class=annottext>x1:MeasuresAndCaseSplitting.ABC -&gt; {o : () | 0 &lt;= MeasuresAndCaseSplitting.toInt x1}</span><span class='hs-definition'>safeBut</span></a> <span class='hs-conid'>A</span>   <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span> 
<span class=hs-linenum>107: </span><span class='hs-definition'>safeBut</span> <span class='hs-keyword'>_</span>   <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span> 
</pre>

Liquid Haskell knows that if the argument `x` is actually an `A`,
then `toInt x` is not negative, but does not know the value of `toInt`
for the default case. 

But, *by default* Liquid Haskell will do the the case expansion 
of the default case for you and rewrite your code to match `_`
with all the possible cases. 
Thus, Liquid Haskell will internally rewrite `safeBut` as 

<pre><span class=hs-linenum>119: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>safeButLH</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>ABC</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{o:</span><span class='hs-conid'>()</span> <span class='hs-keyword'>| 0 &lt;= toInt x}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>120: </span><span class='hs-definition'>safeButLH</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>ABC</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>121: </span><a class=annot href="#"><span class=annottext>x1:MeasuresAndCaseSplitting.ABC -&gt; {o : () | 0 &lt;= MeasuresAndCaseSplitting.toInt x1}</span><span class='hs-definition'>safeButLH</span></a> <span class='hs-conid'>A</span>   <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span> 
<span class=hs-linenum>122: </span><span class='hs-definition'>safeButLH</span> <span class='hs-conid'>B</span>   <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span> 
<span class=hs-linenum>123: </span><span class='hs-definition'>safeButLH</span> <span class='hs-conid'>C</span>   <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span> 
</pre>

With this rewrite Liquid Haskell gets precision!
Thus, it has all the information it needs to prove `safeBut` as safe. 
Yet, it repeats the code of the default case, 
thus verification slows down. 

In this example, we only have three case alternatives, 
so we only repeat the code two times with a minor slow down. 
In cases with many more alternatives repeating the code 
of the default case can kill the verification time. 

For that reason, Liquid Haskell comes with the `no-case-expand`
flag that deactivates this expansion of the default cases. 
With the `no-case-expand` flag on, the `safeBut` code will not type check
and to fix it the user needs to perform the case expansion manually. 

In short, the `no-case-expand` increases verification speed 
but reduces precision. Then it is up to the user 
to manually expand the default cases, as required, 
to restore all the precision required for the code to type check. 

[demo]:              http://goto.ucsd.edu:8090/index.html#?demo=RangeSet.hs


