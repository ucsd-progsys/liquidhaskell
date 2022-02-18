---
layout: post
title: The Hillelogram Verifier Rodeo I (LeftPad) 
date: 2018-05-17
comments: true
author: Ranjit Jhala 
published: true
tags:
   - reflection
demo: LeftPad.hs
---

<!--
<blockquote class="twitter-tweet" data-lang="en"><p lang="en" dir="ltr">You have to provide a 100%, machine-checked guarantee that there are no problems with your code whatsoever. If it&#39;s so much easier to analyze FP programs than imperative programs, this should be simple, right?</p>&mdash; Hillel (@Hillelogram) <a href="https://twitter.com/Hillelogram/status/987432180837167104?ref_src=twsrc%5Etfw">April 20, 2018</a></blockquote>
<script async src="https://platform.twitter.com/widgets.js" charset="utf-8"></script>
-->

A month ago, [Hillel Wayne](https://twitter.com/Hillelogram)
posted a [verification challenge](https://twitter.com/Hillelogram/status/987432180837167104)
comprising three problems that might _sound_ frivolous, 
but which, in fact, hit the sweet spot of being easy to 
describe and yet interesting to implement and verify. 
I had a lot of fun hacking them up in LH, and learned 
some things doing so.

Today, lets see how to implement the first 
of these challenges -- `leftPad` -- in Haskell, 
and to check Hillel's specification with LH. 

(Click here to [demo][demo])

<!-- more -->

<div class="hidden">

<pre><span class=hs-linenum>35: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--reflection"</span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>36: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--ple"</span>         <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>37: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>infixr</span> <span class='hs-varop'>++</span>              <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>38: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>infixr</span> <span class='hs-varop'>!!</span>              <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>39: </span>
<span class=hs-linenum>40: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>PadLeft</span> <span class='hs-keyword'>where</span> 
<span class=hs-linenum>41: </span>
<span class=hs-linenum>42: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>max</span><span class='hs-layout'>,</span> <span class='hs-varid'>replicate</span><span class='hs-layout'>,</span> <span class='hs-layout'>(</span><span class='hs-varop'>++</span><span class='hs-layout'>)</span><span class='hs-layout'>,</span> <span class='hs-layout'>(</span><span class='hs-varop'>!!</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>43: </span><span class='hs-layout'>(</span><span class='hs-varop'>!!</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>44: </span><span class='hs-definition'>size</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>45: </span><span class='hs-layout'>(</span><span class='hs-varop'>++</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>46: </span><span class='hs-definition'>obviously</span>         <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span> 
<span class=hs-linenum>47: </span><span class='hs-definition'>replicate</span>         <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>48: </span><span class='hs-definition'>thmReplicate</span>      <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span> 
<span class=hs-linenum>49: </span><span class='hs-definition'>thmAppLeft</span>        <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>50: </span><span class='hs-definition'>thmAppRight</span>       <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>51: </span><span class='hs-definition'>thmLeftPad</span>        <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>52: </span>
<span class=hs-linenum>53: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reflect</span> <span class='hs-varid'>max</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>54: </span><span class='hs-definition'>max</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> 
<span class=hs-linenum>55: </span><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {VV : GHC.Types.Int | VV == max x1 x2
                                                              &amp;&amp; VV == (if x1 &gt; x2 then x1 else x2)}</span><span class='hs-definition'>max</span></a> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Bool | v &lt;=&gt; x &gt; y}</span><span class='hs-keyword'>if</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Bool | v &lt;=&gt; x &gt; y}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Bool | v &lt;=&gt; x1 &gt; x2}</span><span class='hs-varop'>&gt;</span></a> <span class='hs-varid'>y</span> <span class='hs-keyword'>then</span> <span class='hs-varid'>x</span> <span class='hs-keyword'>else</span> <span class='hs-varid'>y</span> 
<span class=hs-linenum>56: </span>
<span class=hs-linenum>57: </span><span class='hs-comment'>-- A ghost function only used in the specification</span>
<span class=hs-linenum>58: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>leftPadVal</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-keyword'>{Int | False}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>_</span> <span class='hs-keyword'>@-}</span>
</pre>
</div>

The LeftPad Challenge 
---------------------

The first of these problems was 
[leftPad](https://twitter.com/Hillelogram/status/987432181889994759)

<blockquote class="twitter-tweet" data-lang="en"><p lang="en" dir="ltr">1. Leftpad. Takes a padding character, a string, and a total length, returns the string padded with that length with that character. If length is less than string, does nothing.<a href="https://t.co/X8qR8gTZdO">https://t.co/X8qR8gTZdO</a></p>&mdash; Hillel (@Hillelogram) <a href="https://twitter.com/Hillelogram/status/987432181889994759?ref_src=twsrc%5Etfw">April 20, 2018</a></blockquote>
<script async src="https://platform.twitter.com/widgets.js" charset="utf-8"></script>

Implementation 
--------------

First, lets write an idiomatic implementation 
of `leftPad` where we will take the liberty of 
generalizing 

- the **padding character** to be the input `c` that is of some (polymorphic) type `a` 
- the **string** to be the input `xs` that is a list of `a`

If the target length `n` is indeed greater than the input string `xs`, 
i.e. if `k = n - size xs` is positive, we `replicate` the character `c`
`k` times and append the result to the left of the input `xs`. 
Otherwise, if `k` is negative, we do nothing, i.e. return the input.


<pre><span class=hs-linenum>87: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reflect</span> <span class='hs-varid'>leftPad</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>88: </span><span class='hs-definition'>leftPad</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>89: </span><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; a -&gt; x3:[a] -&gt; {res : [a] | size res == max x1 (size x3)}</span><span class='hs-definition'>leftPad</span></a> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>c</span></a> <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>xs</span></a> 
<span class=hs-linenum>90: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>GHC.Types.Bool</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>k</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:a -&gt; {v : [a] | size v == k
                        &amp;&amp; v == replicate k x1
                        &amp;&amp; v == (if 0 == k then [] else : x1 (replicate (k - 1) x1))} | v == replicate k}</span><span class='hs-varid'>replicate</span></a> <span class='hs-varid'>k</span> <span class='hs-varid'>c</span> <span class='hs-varop'>++</span> <span class='hs-varid'>xs</span> 
<span class=hs-linenum>91: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>xs</span> 
<span class=hs-linenum>92: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>93: </span>    <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>k</span></a>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0
                     &amp;&amp; v == size xs}</span><span class='hs-varid'>size</span></a> <span class='hs-varid'>xs</span>
</pre>

The code for `leftPad` is short because we've 
delegated much of the work to `size`, `replicate` 
and `++`. Here's how we can compute the `size` of a list:


<pre><span class=hs-linenum>101: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>size</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>102: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>size</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Nat</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>103: </span><a class=annot href="#"><span class=annottext>x1:[a] -&gt; {v : GHC.Types.Int | v &gt;= 0
                               &amp;&amp; v == size x1}</span><span class='hs-definition'>size</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span> 
<span class=hs-linenum>104: </span><span class='hs-definition'>size</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == (1 : int)}</span><span class='hs-num'>1</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0
                     &amp;&amp; v == size xs}</span><span class='hs-varid'>size</span></a> <span class='hs-varid'>xs</span>
</pre>

and here is the list append function `++` :


<pre><span class=hs-linenum>110: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reflect</span> <span class='hs-varop'>++</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>111: </span><span class='hs-keyword'>{-@</span> <span class='hs-layout'>(</span><span class='hs-varop'>++</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> 
<span class=hs-linenum>112: </span>            <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| size v = size xs + size ys}</span> 
<span class=hs-linenum>113: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>114: </span><span class='hs-conid'>[]</span>     <a class=annot href="#"><span class=annottext>x1:[a] -&gt; x2:[a] -&gt; {v : [a] | size v == size x1 + size x2}</span><span class='hs-varop'>++</span></a> <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>ys</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>ys</span> 
<span class=hs-linenum>115: </span><span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varop'>++</span> <span class='hs-varid'>ys</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>x</span> <span class='hs-conop'>:</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : [a] | size v == size xs + size ys
           &amp;&amp; v == ++ xs ys}</span><span class='hs-varid'>xs</span></a> <span class='hs-varop'>++</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span>
</pre>

and finally the implementation of `replicate` :


<pre><span class=hs-linenum>121: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reflect</span> <span class='hs-varid'>replicate</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>122: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>replicate</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> 
<span class=hs-linenum>123: </span>                 <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| size v = n}</span> 
<span class=hs-linenum>124: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>125: </span><a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; a -&gt; {v : [a] | size v == x1}</span><span class='hs-definition'>replicate</span></a> <span class='hs-num'>0</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>[]</span> 
<span class=hs-linenum>126: </span><span class='hs-definition'>replicate</span> <span class='hs-varid'>n</span> <span class='hs-varid'>c</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>c</span> <span class='hs-conop'>:</span> <a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; a -&gt; {v : [a] | size v == x1}</span><span class='hs-varid'>replicate</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a> <span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varid'>c</span>
</pre>

What shall we Prove? 
--------------------

My eyes roll whenever I read the phrase "proved X (a function, a program) _correct_".

There is no such thing as "correct".

There are only "specifications" or "properties", 
and proofs that ensures that your code matches 
those specifications or properties.

What _specifications_ shall we verify about our 
implementation of `leftPad`? One might argue that 
the above code is "obviously correct", i.e. the 
implementation more or less directly matches the 
informal requirements. 

One way to formalize this notion of "obviously correct" 
is to verify a specification that directly captures 
the informal requirements: 


<pre><span class=hs-linenum>151: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>obviously</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>c</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> 
<span class=hs-linenum>152: </span>      <span class='hs-keyword'>{ leftPad n c xs = if (size xs &lt; n) 
                         then (replicate (n - size xs) c ++ xs) 
                         else xs }</span> 
<span class=hs-linenum>155: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>156: </span><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:a -&gt; x3:[a] -&gt; {VV : () | leftPad x1 x2 x3 == (if size x3 &lt; x1 then ++ (replicate (x1 - size x3) x2) x3 else x3)}</span><span class='hs-definition'>obviously</span></a> <span class='hs-keyword'>_</span> <span class='hs-keyword'>_</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span> 
</pre>

In the above, the type signature is a specification 
that says that for all `n`, `c` and `xs`, the value 
returned by `leftPad n c xs` is `xs` when `n` is 
too small, and the suitably padded definition otherwise. 

The code, namely `()`, is the proof. 
LH is able to trivially check that `leftPad` 
meets the "obviously correct" specification, 
because, well, in this case, the implementation 
_is_ the specification. (Incidentally, this 
is also why the [Idris solution][idris-leftpad] 
is terse.)

So, if you are happy with the above specification, 
you can stop reading right here: we're done. 

Hillel's Specifications 
-----------------------

However, the verification rodeo is made more 
interesting by Hillel's [Dafny specifications][dafny-leftpad]:

1. **Size** The `size` of the returned sequence is the 
   larger of `n` and the size of `xs`;

2. **Pad-Value** Let `K = n - size xs`. We require 
   that the `i`-th element of the padded-sequence 
   is `c` if `0 <= i < K`, and is the `i - K`-th 
   element of `xs` otherwise.

<div class="row-fluid">
  <div class="span12 pagination-centered">
  <img src="../../static/img/leftpad-spec.png"
       alt="Ribbons" height="150">
  </div>
</div>


Digression: The Importance of being Decidable 
---------------------------------------------

LH, like many of the other rodeo entries, uses 
SMT solvers to automate verification. For example, 
the `leftPad` solutions in [Dafny][dafny-leftpad] 
and [SPARK][spark-leftpad] and [F*][fstar-leftpad] 
make heavy use [quantified axioms to encode properties 
of sequences.][dafny-seq-axioms] 

However, unlike its many SMT-based brethren, LH 
takes a somewhat fanatical stance: it _never_ uses 
quantifiers or axioms. We take this rigid position
because SMT solvers are only _predictable_ on 
queries from (certain) **decidable logics**.
Axioms, or more generally, quantified formulas 
rapidly take SMT solvers out of this "comfort zone",
causing them to reject valid formulas, run slowly, 
or even, [to run forever][regehr-tweet].

<!--
<blockquote class="twitter-tweet" data-lang="en"><p lang="en" dir="ltr">I mean, I&#39;m somewhat kind of serious here, I think unneeded generality makes things really difficult often. as a random example quantifiers seem to throw z3 into a really bad place, even when they&#39;re easy ones.</p>&mdash; John Regehr (@johnregehr) <a href="https://twitter.com/johnregehr/status/996901816842440704?ref_src=twsrc%5Etfw">May 16, 2018</a></blockquote>
<script async src="https://platform.twitter.com/widgets.js" charset="utf-8"></script>

<div class="row-fluid">
  <div class="span12 pagination-centered">
  <img src="../../static/img/regehr-tweet-quantifiers.png"
       alt="Ribbons" height="100">
  </div>
</div>
-->

Thus, we have chosen to deliberately avoid 
the siren song of quantifiers by lashing LH 
firmly to the steady mast of decidable logics.

Reasoning about Sequences 
-------------------------

Unfortunately, this design choice leaves us 
with some work: we must develop i.e. _state_ 
and _prove_ relevant properties about sequences 
from scratch.

**Indexing into a Sequence**

To start, lets define the notion of the `i`-th element of 
a sequence (this is pretty much Haskell's list-index operator)


<pre><span class=hs-linenum>247: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reflect</span> <span class='hs-varop'>!!</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>248: </span><span class='hs-keyword'>{-@</span> <span class='hs-layout'>(</span><span class='hs-varop'>!!</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{n:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| n &lt; size xs}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>249: </span><span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span><span class='hs-layout'>)</span>  <a class=annot href="#"><span class=annottext>x1:[a] -&gt; {v : GHC.Types.Int | v &gt;= 0
                               &amp;&amp; v &lt; size x1} -&gt; a</span><span class='hs-varop'>!!</span></a> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>x</span> 
<span class=hs-linenum>250: </span><span class='hs-layout'>(</span><span class='hs-keyword'>_</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varop'>!!</span> <span class='hs-varid'>n</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:[a] -&gt; {v : GHC.Types.Int | v &gt;= 0
                               &amp;&amp; v &lt; size x1} -&gt; a</span><span class='hs-varid'>xs</span></a> <span class='hs-varop'>!!</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a> <span class='hs-num'>1</span><span class='hs-layout'>)</span>
</pre>

**Replicated Sequences** 

Next, we verify that _every_ element in a `replicate`-d 
sequence is the element being cloned:


<pre><span class=hs-linenum>259: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>thmReplicate</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>c</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-keyword'>{Nat | i &lt; n}</span> <span class='hs-keyglyph'>-&gt;</span> 
<span class=hs-linenum>260: </span>                    <span class='hs-keyword'>{ replicate n c !! i  == c }</span> 
<span class=hs-linenum>261: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>262: </span><a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; x2:a -&gt; x3:{v : GHC.Types.Int | v &gt;= 0
                                                                   &amp;&amp; v &lt; x1} -&gt; {VV : () | !! (replicate x1 x2) x3 == x2}</span><span class='hs-definition'>thmReplicate</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>c</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0
                     &amp;&amp; v &lt; n}</span><span class='hs-varid'>i</span></a> 
<span class=hs-linenum>263: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>GHC.Types.Bool</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Bool | v &lt;=&gt; x1 == x2}</span><span class='hs-varop'>==</span></a> <span class='hs-num'>0</span>    <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>264: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{v : GHC.Types.Int | v &gt;= 0} -&gt; x2:a -&gt; x3:{v : GHC.Types.Int | v &gt;= 0
                                                                   &amp;&amp; v &lt; x1} -&gt; {VV : () | !! (replicate x1 x2) x3 == x2}</span><span class='hs-varid'>thmReplicate</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a> <span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varid'>c</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a> <span class='hs-num'>1</span><span class='hs-layout'>)</span> 
</pre>

LH verifies the above "proof by induction": 

- In the base case `i == 0` and the value returned is `c` 
  by the definition of `replicate` and `!!`. 
  
- In the inductive case, `replicate n c !! i` is equal to 
  `replicate (n-1) c !! (i-1)` which, by the "induction hypothesis" 
  (i.e. by recursively calling the theorem) is `c`.

**Concatenating Sequences** 

Finally, we need two properties that relate 
concatenation and appending, namely, the 
`i`-th element of `xs ++ ys` is: 

- **Left** the `i`-th element of `xs` if `0 <= i < size xs`, and 
- **Right** the `i - size xs` element of `ys` otherwise.


<pre><span class=hs-linenum>286: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>thmAppLeft</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{i:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| i &lt; size xs}</span> <span class='hs-keyglyph'>-&gt;</span> 
<span class=hs-linenum>287: </span>                  <span class='hs-keyword'>{ (xs ++ ys) !! i == xs !! i }</span> 
<span class=hs-linenum>288: </span>  <span class='hs-keyword'>@-}</span> 
<span class=hs-linenum>289: </span><a class=annot href="#"><span class=annottext>x1:[a] -&gt; x2:[a] -&gt; x3:{v : GHC.Types.Int | v &gt;= 0
                                            &amp;&amp; v &lt; size x1} -&gt; {VV : () | !! (++ x1 x2) x3 == !! x1 x3}</span><span class='hs-definition'>thmAppLeft</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>ys</span></a> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span> 
<span class=hs-linenum>290: </span><span class='hs-definition'>thmAppLeft</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varid'>ys</span> <span class='hs-varid'>i</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:[a] -&gt; x2:[a] -&gt; x3:{v : GHC.Types.Int | v &gt;= 0
                                            &amp;&amp; v &lt; size x1} -&gt; {VV : () | !! (++ x1 x2) x3 == !! x1 x3}</span><span class='hs-varid'>thmAppLeft</span></a> <span class='hs-varid'>xs</span> <span class='hs-varid'>ys</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span>      
<span class=hs-linenum>291: </span>
<span class=hs-linenum>292: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>thmAppRight</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{i:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| size xs &lt;= i}</span> <span class='hs-keyglyph'>-&gt;</span> 
<span class=hs-linenum>293: </span>                   <span class='hs-keyword'>{ (xs ++ ys) !! i == ys !! (i - size xs) }</span> 
<span class=hs-linenum>294: </span>  <span class='hs-keyword'>@-}</span> 
<span class=hs-linenum>295: </span><a class=annot href="#"><span class=annottext>x1:[a] -&gt; x2:[a] -&gt; x3:{v : GHC.Types.Int | v &gt;= 0
                                            &amp;&amp; size x1 &lt;= v} -&gt; {VV : () | !! (++ x1 x2) x3 == !! x2 (x3 - size x1)}</span><span class='hs-definition'>thmAppRight</span></a> <span class='hs-conid'>[]</span>     <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>ys</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0}</span><span class='hs-varid'>i</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span> 
<span class=hs-linenum>296: </span><span class='hs-definition'>thmAppRight</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varid'>ys</span> <span class='hs-varid'>i</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:[a] -&gt; x2:[a] -&gt; x3:{v : GHC.Types.Int | v &gt;= 0
                                            &amp;&amp; size x1 &lt;= v} -&gt; {VV : () | !! (++ x1 x2) x3 == !! x2 (x3 - size x1)}</span><span class='hs-varid'>thmAppRight</span></a> <span class='hs-varid'>xs</span> <span class='hs-varid'>ys</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span>      
</pre>

Both of the above properties are proved by induction on `i`.

Proving Hillel's Specifications 
-------------------------------

Finally, we're ready to state and prove Hillel's specifications. 

**Size Specification**

The size specification is straightforward, in that LH proves 
it automatically, when type-checking `leftPad` against the 
signature:


<pre><span class=hs-linenum>313: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>leftPad</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>c</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> 
<span class=hs-linenum>314: </span>                <span class='hs-keyword'>{res:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| size res = max n (size xs)}</span> 
<span class=hs-linenum>315: </span>  <span class='hs-keyword'>@-}</span>
</pre>

**Pad-Value Specification**

We _specify_ the pad-value property -- i.e. the `i`-th 
element equals `c` or the corresponding element of `xs` -- 
by a type signature:


<pre><span class=hs-linenum>325: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>thmLeftPad</span> 
<span class=hs-linenum>326: </span>      <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>c</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyword'>{size xs &lt; n}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-keyword'>{Nat | i &lt; n}</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>327: </span>         <span class='hs-keyword'>{ leftPad n c xs !! i ==  leftPadVal n c xs i }</span>                               
<span class=hs-linenum>328: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>329: </span>
<span class=hs-linenum>330: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reflect</span> <span class='hs-varid'>leftPadVal</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>331: </span><a class=annot href="#"><span class=annottext>{n : GHC.Types.Int | False} -&gt; a -&gt; [a] -&gt; GHC.Types.Int -&gt; a</span><span class='hs-definition'>leftPadVal</span></a> <a class=annot href="#"><span class=annottext>{n : GHC.Types.Int | False}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>c</span></a> <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>i</span></a> 
<span class=hs-linenum>332: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Bool | v &lt;=&gt; i &lt; k}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>k</span>     <span class='hs-keyglyph'>=</span> <span class='hs-varid'>c</span> 
<span class=hs-linenum>333: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : [a] | size v &gt;= 0
           &amp;&amp; len v &gt;= 0
           &amp;&amp; v == xs}</span><span class='hs-varid'>xs</span></a> <span class='hs-varop'>!!</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v == i - k}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a> <span class='hs-varid'>k</span><span class='hs-layout'>)</span>
<span class=hs-linenum>334: </span>  <span class='hs-keyword'>where</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>k</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0
                     &amp;&amp; v == size xs}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a> <span class='hs-varid'>size</span> <span class='hs-varid'>xs</span> 
</pre>

**Pad-Value Verification**

We _verify_ the above property by filling in the 
implementation of `thmLeftPad` as:


<pre><span class=hs-linenum>343: </span><a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:a -&gt; x3:{v : [a] | size v &lt; x1} -&gt; x4:{v : GHC.Types.Int | v &gt;= 0
                                                                                  &amp;&amp; v &lt; x1} -&gt; {VV : () | !! (leftPad x1 x2 x3) x4 == leftPadVal x1 x2 x3 x4}</span><span class='hs-definition'>thmLeftPad</span></a> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>c</span></a> <a class=annot href="#"><span class=annottext>{v : [a] | size v &lt; n}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0
                     &amp;&amp; v &lt; n}</span><span class='hs-varid'>i</span></a> 
<span class=hs-linenum>344: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Bool | v &lt;=&gt; i &lt; k}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>k</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:[a] -&gt; x2:{v : GHC.Types.Int | v &gt;= 0
                                  &amp;&amp; v &lt; size cs} -&gt; {v : () | !! (++ cs x1) x2 == !! cs x2}</span><span class='hs-varid'>thmAppLeft</span></a>  <span class='hs-varid'>cs</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>i</span> <span class='hs-varop'>`seq`</span> <a class=annot href="#"><span class=annottext>x1:a -&gt; x2:{v : GHC.Types.Int | v &gt;= 0
                                &amp;&amp; v &lt; k} -&gt; {v : () | !! (replicate k x1) x2 == x1}</span><span class='hs-varid'>thmReplicate</span></a> <span class='hs-varid'>k</span> <span class='hs-varid'>c</span> <span class='hs-varid'>i</span>   
<span class=hs-linenum>345: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:[a] -&gt; x2:{v : GHC.Types.Int | v &gt;= 0
                                  &amp;&amp; size cs &lt;= v} -&gt; {v : () | !! (++ cs x1) x2 == !! x1 (x2 - size cs)}</span><span class='hs-varid'>thmAppRight</span></a> <span class='hs-varid'>cs</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>i</span>
<span class=hs-linenum>346: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>347: </span>    <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>k</span></a>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>GHC.Types.Int</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:GHC.Types.Int -&gt; x2:GHC.Types.Int -&gt; {v : GHC.Types.Int | v == x1 - x2}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{v : GHC.Types.Int | v &gt;= 0
                     &amp;&amp; v == size xs}</span><span class='hs-varid'>size</span></a> <span class='hs-varid'>xs</span> 
<span class=hs-linenum>348: </span>    <a class=annot href="#"><span class=annottext>{v : [a] | size v == k
           &amp;&amp; v == replicate k c
           &amp;&amp; v == (if 0 == k then [] else : c (replicate (k - 1) c))}</span><span class='hs-varid'>cs</span></a>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:a -&gt; {v : [a] | size v == k
                        &amp;&amp; v == replicate k x1
                        &amp;&amp; v == (if 0 == k then [] else : x1 (replicate (k - 1) x1))} | v == replicate k}</span><span class='hs-varid'>replicate</span></a> <span class='hs-varid'>k</span> <span class='hs-varid'>c</span>
</pre>

The "proof"  -- in quotes because its 
just a Haskell function -- simply combines 
the replicate- and concatenate-left theorems 
if `i` is in the "pad", and the concatenate-right 
theorem, otherwise.

Conclusions 
-----------

That concludes part I of the rodeo. What did I learn from this exercise?

1. Even apparently simple functions like `leftPad` can 
   have _many_ different specifications; there is no 
   necessarily "best" specification as different specs 
   make different assumptions about what is "trusted", 
   and more importantly, though we didn't see it here, 
   ultimately a spec is a particular _view_ into how a 
   piece of code behaves and 
   we may want different views depending on the context where we want 
   to use the given piece of code.

2. The `leftPad` exercise illustrates a fundamental 
   problem with Floyd-Hoare style "modular" verification, 
   where pre- and post-conditions (or contracts or refinement 
   types or ...) are used to modularly "abstract" functions 
   i.e. are used to describe the behavior of a function 
   at a call-site. As the above exercise shows, we often 
   need properties connecting the behavior of different 
   functions, e.g. append (`++`), indexing (`!!`). 
   In these cases, the only meaningful _specification_ 
   for the underlying function _is its implementation_.

3. Finally, the above proofs are all over user-defined 
   recursive functions which this was not even possible 
   before [refinement reflection][tag-reflection], i.e 
   till about a year ago. I'm also quite pleased by how 
   [logical evaluation][tag-ple] makes these proofs 
   quite short, letting LH verify expressive specifications 
   while steering clear of the siren song of quantifiers.

[demo]:             http://goto.ucsd.edu:8090/index.html#?demo=LeftPad.hs
[dafny-leftpad]:    https://rise4fun.com/Dafny/nbNTl
[spark-leftpad]:    https://blog.adacore.com/taking-on-a-challenge-in-spark
[fstar-leftpad]:    https://gist.github.com/graydon/901f98049d05db65d9a50f741c7f7626
[idris-leftpad]:    https://github.com/hwayne/lets-prove-leftpad/blob/master/idris/Leftpad.idr
[dafny-seq-axioms]: https://github.com/Microsoft/dafny/blob/master/Binaries/DafnyPrelude.bpl#L898-L1110
[tag-reflection]:   /tags/reflection.html
[tag-ple]:          /tags/ple.html
[regehr-tweet]:     https://twitter.com/johnregehr/status/996901816842440704
