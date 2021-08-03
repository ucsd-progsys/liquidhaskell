---
layout: post
title: Pointers Gone Wild
date: 2014-05-28
comments: true
author: Eric Seidel
published: true
tags:
   - benchmarks
   - text
demo: TextInternal.hs
---

A large part of the allure of Haskell is its elegant, high-level ADTs
that ensure[^compilercorrectness] that programs won't be plagued by problems
like the infamous [SSL heartbleed bug](http://en.wikipedia.org/wiki/Heartbleed).

[^compilercorrectness]: Assuming the absence of errors in the compiler and run-time...

However, another part of Haskell's charm is that when you really really 
need to, you can drop down to low-level pointer twiddling to squeeze the 
most performance out of your machine. But of course, that opens the door 
to the #heartbleeds.

Can we have have our cake and eat it too? 

Can we twiddle pointers and still get the nice safety assurances of high-level types?

<!-- more -->

To understand the potential for potential bleeding,
let's study the popular `text` library for efficient 
text processing. The library provides the high-level 
API Haskellers have come to expect while using stream 
fusion and byte arrays under the hood to guarantee 
high performance.

Suppose we wanted to get the *i*th `Char` of a `Text`,
 we could write a function[^bad]
<pre><span class=hs-linenum>39: </span><span class='hs-definition'>charAt</span> <span class='hs-layout'>(</span><span class='hs-conid'>Text</span> <span class='hs-varid'>a</span> <span class='hs-varid'>o</span> <span class='hs-varid'>l</span><span class='hs-layout'>)</span> <span class='hs-varid'>i</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>word2char</span> <span class='hs-varop'>$</span> <span class='hs-varid'>unsafeIndex</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-varid'>o</span><span class='hs-varop'>+</span><span class='hs-varid'>i</span><span class='hs-layout'>)</span>
<span class=hs-linenum>40: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>41: </span>    <span class='hs-varid'>word2char</span>         <span class='hs-keyglyph'>=</span> <span class='hs-varid'>chr</span> <span class='hs-varop'>.</span> <span class='hs-varid'>fromIntegral</span>
</pre>
which extracts the underlying array `a`, indexes into it starting
at the offset `o` and casts the `Word16` to a `Char`, using 
functions exported by `text`.

[^bad]: This function is bad for numerous reasons, least of which is that `Data.Text.index` is already provided, but stay with us...

Let's try this out in GHCi.
<pre><span class=hs-linenum>50: </span><span class='hs-definition'>ghci</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>let</span> <span class='hs-varid'>t</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>pack</span> <span class='hs-keyglyph'>[</span><span class='hs-chr'>'d'</span><span class='hs-layout'>,</span><span class='hs-chr'>'o'</span><span class='hs-layout'>,</span><span class='hs-chr'>'g'</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>51: </span><span class='hs-definition'>ghci</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>charAt</span> <span class='hs-varid'>t</span> <span class='hs-num'>0</span>
<span class=hs-linenum>52: </span><span class='hs-chr'>'d'</span>
<span class=hs-linenum>53: </span><span class='hs-definition'>ghci</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>charAt</span> <span class='hs-varid'>t</span> <span class='hs-num'>2</span>
<span class=hs-linenum>54: </span><span class='hs-chr'>'g'</span>
</pre>

Looks good so far, what happens if we keep going?
<pre><span class=hs-linenum>58: </span><span class='hs-definition'>ghci</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>charAt</span> <span class='hs-varid'>t</span> <span class='hs-num'>3</span>
<span class=hs-linenum>59: </span><span class='hs-chr'>'\NUL'</span>
<span class=hs-linenum>60: </span><span class='hs-definition'>ghci</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>charAt</span> <span class='hs-varid'>t</span> <span class='hs-num'>100</span>
<span class=hs-linenum>61: </span><span class='hs-chr'>'\8745'</span>
</pre>

Oh dear, not only did we not get any sort of exception from Haskell, 
we weren't even stopped by the OS with a segfault. This is quite 
dangerous since we have no idea what sort of data we just read! 
To be fair to the library's authors, we did use a function that 
was clearly branded `unsafe`, but these functions, while not 
intended for *clients*, pervade the implementation of the *library*.

Wouldn't it be nice to have these last two calls *rejected at compile time*?

In this post we'll see exactly how prevent invalid memory accesses 
like this with LiquidHaskell.


<div class="hidden">


<pre><span class=hs-linenum>80: </span><span class='hs-comment'>{-# LANGUAGE BangPatterns, MagicHash, Rank2Types,
    RecordWildCards, UnboxedTuples, ExistentialQuantification #-}</span>
<span class=hs-linenum>82: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-termination"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>83: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>TextInternal</span> <span class='hs-layout'>(</span><span class='hs-varid'>test</span><span class='hs-layout'>,</span> <span class='hs-varid'>goodMain</span><span class='hs-layout'>,</span> <span class='hs-varid'>badMain</span><span class='hs-layout'>,</span> <span class='hs-varid'>charAt</span><span class='hs-layout'>,</span> <span class='hs-varid'>charAt'</span><span class='hs-layout'>)</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>84: </span>
<span class=hs-linenum>85: </span><span class='hs-keyword'>import</span> <span class='hs-keyword'>qualified</span> <span class='hs-conid'>Control</span><span class='hs-varop'>.</span><span class='hs-conid'>Exception</span> <span class='hs-keyword'>as</span> <span class='hs-conid'>Ex</span>
<span class=hs-linenum>86: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Control</span><span class='hs-varop'>.</span><span class='hs-conid'>Applicative</span>     <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varop'>&lt;$&gt;</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>87: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Control</span><span class='hs-varop'>.</span><span class='hs-conid'>Monad</span>           <span class='hs-layout'>(</span><span class='hs-varid'>when</span><span class='hs-layout'>)</span>
<span class=hs-linenum>88: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Control</span><span class='hs-varop'>.</span><span class='hs-conid'>Monad</span><span class='hs-varop'>.</span><span class='hs-conid'>ST</span><span class='hs-varop'>.</span><span class='hs-conid'>Unsafe</span> <span class='hs-layout'>(</span><span class='hs-varid'>unsafeIOToST</span><span class='hs-layout'>)</span>
<span class=hs-linenum>89: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Bits</span> <span class='hs-layout'>(</span><span class='hs-varid'>shiftR</span><span class='hs-layout'>,</span> <span class='hs-varid'>xor</span><span class='hs-layout'>,</span> <span class='hs-layout'>(</span><span class='hs-varop'>.&amp;.</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>90: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Char</span>
<span class=hs-linenum>91: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Foreign</span><span class='hs-varop'>.</span><span class='hs-conid'>C</span><span class='hs-varop'>.</span><span class='hs-conid'>Types</span> <span class='hs-layout'>(</span><span class='hs-conid'>CSize</span><span class='hs-layout'>)</span>
<span class=hs-linenum>92: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>GHC</span><span class='hs-varop'>.</span><span class='hs-conid'>Base</span> <span class='hs-layout'>(</span><span class='hs-conid'>Int</span><span class='hs-layout'>(</span><span class='hs-keyglyph'>..</span><span class='hs-layout'>)</span><span class='hs-layout'>,</span> <span class='hs-conid'>ByteArray</span><span class='hs-cpp'>#</span><span class='hs-layout'>,</span> <span class='hs-conid'>MutableByteArray</span><span class='hs-cpp'>#</span><span class='hs-layout'>,</span> <span class='hs-varid'>newByteArray</span><span class='hs-cpp'>#</span><span class='hs-layout'>,</span>
<span class=hs-linenum>93: </span>                 <span class='hs-varid'>writeWord16Array</span><span class='hs-cpp'>#</span><span class='hs-layout'>,</span> <span class='hs-varid'>indexWord16Array</span><span class='hs-cpp'>#</span><span class='hs-layout'>,</span> <span class='hs-varid'>unsafeCoerce</span><span class='hs-cpp'>#</span><span class='hs-layout'>,</span> <span class='hs-varid'>ord</span><span class='hs-layout'>,</span>
<span class=hs-linenum>94: </span>                 <span class='hs-varid'>iShiftL</span><span class='hs-cpp'>#</span><span class='hs-layout'>)</span>
<span class=hs-linenum>95: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>GHC</span><span class='hs-varop'>.</span><span class='hs-conid'>ST</span> <span class='hs-layout'>(</span><span class='hs-conid'>ST</span><span class='hs-layout'>(</span><span class='hs-keyglyph'>..</span><span class='hs-layout'>)</span><span class='hs-layout'>,</span> <span class='hs-varid'>runST</span><span class='hs-layout'>)</span>
<span class=hs-linenum>96: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>GHC</span><span class='hs-varop'>.</span><span class='hs-conid'>Word</span> <span class='hs-layout'>(</span><span class='hs-conid'>Word16</span><span class='hs-layout'>(</span><span class='hs-keyglyph'>..</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>97: </span>
<span class=hs-linenum>98: </span><span class='hs-keyword'>import</span> <span class='hs-keyword'>qualified</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Text</span><span class='hs-varop'>.</span><span class='hs-conid'>Lazy</span><span class='hs-varop'>.</span><span class='hs-conid'>IO</span> <span class='hs-keyword'>as</span> <span class='hs-conid'>TIO</span>
<span class=hs-linenum>99: </span><span class='hs-keyword'>import</span> <span class='hs-keyword'>qualified</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Text</span> <span class='hs-keyword'>as</span> <span class='hs-conid'>T</span>
<span class=hs-linenum>100: </span><span class='hs-keyword'>import</span> <span class='hs-keyword'>qualified</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Text</span><span class='hs-varop'>.</span><span class='hs-conid'>Internal</span> <span class='hs-keyword'>as</span> <span class='hs-conid'>T</span>
<span class=hs-linenum>101: </span>
<span class=hs-linenum>102: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span>
<span class=hs-linenum>103: </span>
<span class=hs-linenum>104: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>aLen</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-conop'>:</span><span class='hs-conid'>Array</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| v = (aLen a)}</span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>105: </span>
<span class=hs-linenum>106: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maLen</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-conop'>:</span><span class='hs-conid'>MArray</span> <span class='hs-varid'>s</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| v = (maLen a)}</span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>107: </span>
<span class=hs-linenum>108: </span><span class='hs-definition'>new</span>          <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>s</span><span class='hs-varop'>.</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>ST</span> <span class='hs-varid'>s</span> <span class='hs-layout'>(</span><span class='hs-conid'>MArray</span> <span class='hs-varid'>s</span><span class='hs-layout'>)</span>
<span class=hs-linenum>109: </span><span class='hs-definition'>unsafeWrite</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>MArray</span> <span class='hs-varid'>s</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Word16</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>ST</span> <span class='hs-varid'>s</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>110: </span><span class='hs-definition'>unsafeFreeze</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>MArray</span> <span class='hs-varid'>s</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>ST</span> <span class='hs-varid'>s</span> <span class='hs-conid'>Array</span>
<span class=hs-linenum>111: </span><span class='hs-definition'>unsafeIndex</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Array</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Word16</span>
<span class=hs-linenum>112: </span><span class='hs-definition'>copyM</span>        <span class='hs-keyglyph'>::</span> <span class='hs-conid'>MArray</span> <span class='hs-varid'>s</span>               <span class='hs-comment'>-- ^ Destination</span>
<span class=hs-linenum>113: </span>             <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>                    <span class='hs-comment'>-- ^ Destination offset</span>
<span class=hs-linenum>114: </span>             <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>MArray</span> <span class='hs-varid'>s</span>               <span class='hs-comment'>-- ^ Source</span>
<span class=hs-linenum>115: </span>             <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>                    <span class='hs-comment'>-- ^ Source offset</span>
<span class=hs-linenum>116: </span>             <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>                    <span class='hs-comment'>-- ^ Count</span>
<span class=hs-linenum>117: </span>             <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>ST</span> <span class='hs-varid'>s</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>118: </span>
<span class=hs-linenum>119: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>memcpyM</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>MutableByteArray</span><span class='hs-cpp'>#</span> <span class='hs-varid'>s</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>CSize</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>MutableByteArray</span><span class='hs-cpp'>#</span> <span class='hs-varid'>s</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>CSize</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>CSize</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IO</span> <span class='hs-conid'>()</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>120: </span><span class='hs-definition'>memcpyM</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>MutableByteArray</span><span class='hs-cpp'>#</span> <span class='hs-varid'>s</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>CSize</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>MutableByteArray</span><span class='hs-cpp'>#</span> <span class='hs-varid'>s</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>CSize</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>CSize</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IO</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>121: </span><a class=annot href="#"><span class=annottext>forall a.
(MutableByteArray# a)
-&gt; CSize -&gt; (MutableByteArray# a) -&gt; CSize -&gt; CSize -&gt; (IO ())</span><span class='hs-definition'>memcpyM</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a. a</span><span class='hs-varid'>undefined</span></a>
<span class=hs-linenum>122: </span>
<span class=hs-linenum>123: </span><span class='hs-comment'>--------------------------------------------------------------------------------</span>
<span class=hs-linenum>124: </span><span class='hs-comment'>--- Helper Code</span>
<span class=hs-linenum>125: </span><span class='hs-comment'>--------------------------------------------------------------------------------</span>
<span class=hs-linenum>126: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>shiftL</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| ((n = 1) =&gt; (v = (i * 2)))}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>127: </span><span class='hs-definition'>shiftL</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>128: </span><a class=annot href="#"><span class=annottext>x1:{v : Int | (v &gt;= 0)}
-&gt; x2:{v : Int | (v &gt;= 0)}
-&gt; {v : Int | ((x2 == 1) =&gt; (v == (x1 * 2))) &amp;&amp; (v &gt;= 0)}</span><span class='hs-definition'>shiftL</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a. a</span><span class='hs-varid'>undefined</span></a> <span class='hs-comment'>-- (I# x#) (I# i#) = I# (x# `iShiftL#` i#)</span>
<span class=hs-linenum>129: </span>
<span class=hs-linenum>130: </span><span class='hs-definition'>pack</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>String</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Text</span>
<span class=hs-linenum>131: </span><a class=annot href="#"><span class=annottext>x1:[Char] -&gt; {v : Text | ((tLen v) == (len x1))}</span><span class='hs-definition'>pack</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a. a</span><span class='hs-varid'>undefined</span></a> <span class='hs-comment'>-- not "actually" using</span>
<span class=hs-linenum>132: </span>
<span class=hs-linenum>133: </span><a class=annot href="#"><span class=annottext>forall a. {v : Bool | ((Prop v))} -&gt; a -&gt; a</span><span class='hs-definition'>assert</span></a> <a class=annot href="#"><span class=annottext>{v : Bool | ((Prop v))}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>a</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>Bool -&gt; a -&gt; a</span><span class='hs-conid'>Ex</span></a><span class='hs-varop'>.</span><span class='hs-varid'>assert</span> <a class=annot href="#"><span class=annottext>{x3 : Bool | ((Prop x3)) &amp;&amp; (x3 == b)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a>
<span class=hs-linenum>134: </span>
<span class=hs-linenum>135: </span>
<span class=hs-linenum>136: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>Text</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Text</span> <span class='hs-conid'>Array</span> <span class='hs-conid'>Int</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>137: </span>
<span class=hs-linenum>138: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>tLength</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>t</span><span class='hs-conop'>:</span><span class='hs-conid'>Text</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyword'>_</span> <span class='hs-keyword'>| v = (tLen t)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>139: </span><a class=annot href="#"><span class=annottext>x1:Text -&gt; {v : Int | (v == (tLen x1))}</span><span class='hs-definition'>tLength</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Text</span> <span class='hs-keyword'>_</span> <span class='hs-keyword'>_</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span>  <span class='hs-keyglyph'>=</span>  <a class=annot href="#"><span class=annottext>{x3 : Int | (x3 == n) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>n</span></a>
</pre>

</div>

The `Text` Lifecycle
--------------------
`text` splits the reading and writing array operations between two
types of arrays, immutable `Array`s and mutable `MArray`s. This leads to
the following general lifecycle:

![The lifecycle of a `Text`](../static/img/text-lifecycle.png)

The main four array operations we care about are:

1. **creating** an `MArray`,
2. **writing** into an `MArray`,
3. **freezing** an `MArray` into an `Array`, and
4. **reading** from an `Array`.

Creating an `MArray`
--------------------

The (mutable) `MArray` is a thin wrapper around GHC's primitive
`MutableByteArray#`, additionally carrying the number of `Word16`s it
can store.


<pre><span class=hs-linenum>167: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>MArray</span> <span class='hs-varid'>s</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>MArray</span> <span class='hs-layout'>{</span> <a class=annot href="#"><span class=annottext>forall a. (MArray a) -&gt; (MutableByteArray# a)</span><span class='hs-varid'>maBA</span></a>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>MutableByteArray</span><span class='hs-cpp'>#</span> <span class='hs-varid'>s</span>
<span class=hs-linenum>168: </span>                       <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>forall a.
x1:(MArray a) -&gt; {v : Int | (v == (maLen x1)) &amp;&amp; (v &gt;= 0)}</span><span class='hs-varid'>maLen</span></a> <span class='hs-keyglyph'>::</span> <span class='hs-varop'>!</span><span class='hs-conid'>Int</span>
<span class=hs-linenum>169: </span>                       <span class='hs-layout'>}</span>
</pre>

It doesn't make any sense to have a negative length, so we *refine*
the data definition to require that `maLen` be non-negative. 


<pre><span class=hs-linenum>176: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>MArray</span> <span class='hs-varid'>s</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>MArray</span> <span class='hs-layout'>{</span> <span class='hs-varid'>maBA</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>MutableByteArray</span><span class='hs-cpp'>#</span> <span class='hs-varid'>s</span>
<span class=hs-linenum>177: </span>                           <span class='hs-layout'>,</span> <span class='hs-varid'>maLen</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Nat</span>
<span class=hs-linenum>178: </span>                           <span class='hs-layout'>}</span>
<span class=hs-linenum>179: </span>  <span class='hs-keyword'>@-}</span>
</pre>


 As an added bonus, the above specification generates **field-accessor measures** that we will use inside the refined types:
<pre><span class=hs-linenum>184: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>maLen</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>MArray</span> <span class='hs-varid'>s</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>185: </span>    <span class='hs-varid'>maLen</span> <span class='hs-layout'>(</span><span class='hs-conid'>MArray</span> <span class='hs-varid'>a</span> <span class='hs-varid'>l</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>l</span>
<span class=hs-linenum>186: </span>  <span class='hs-keyword'>@-}</span>
</pre>

We can use these accessor measures to define `MArray`s of size `N`:


<pre><span class=hs-linenum>192: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>MArrayN</span> <span class='hs-varid'>a</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>MArray</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>maLen</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

and we can use the above alias, to write a type that tracks the size
of an `MArray` at the point where it is created:


<pre><span class=hs-linenum>199: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>new</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>s</span><span class='hs-varop'>.</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>ST</span> <span class='hs-varid'>s</span> <span class='hs-layout'>(</span><span class='hs-conid'>MArrayN</span> <span class='hs-varid'>s</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>200: </span><a class=annot href="#"><span class=annottext>forall a.
x1:{v : Int | (v &gt;= 0)}
-&gt; (ST a {v : (MArray a) | ((maLen v) == x1)})</span><span class='hs-definition'>new</span></a> <a class=annot href="#"><span class=annottext>{v : Int | (v &gt;= 0)}</span><span class='hs-varid'>n</span></a>
<span class=hs-linenum>201: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x3 : Int | (x3 == n) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x1:Bool
-&gt; x2:Bool
-&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (((Prop x1)) || ((Prop x2))))}</span><span class='hs-varop'>||</span></a> <a class=annot href="#"><span class=annottext>{x3 : Int | (x3 == n) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>Int -&gt; Int -&gt; Int</span><span class='hs-varop'>.&amp;.</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == highBit)}</span><span class='hs-varid'>highBit</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 /= x2))}</span><span class='hs-varop'>/=</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[Char] -&gt; {x1 : (ST a {x2 : (MArray a) | false}) | false}</span><span class='hs-varid'>error</span></a> <a class=annot href="#"><span class=annottext>{x2 : [Char] | ((len x2) &gt;= 0)}</span><span class='hs-str'>"size overflow"</span></a>
<span class=hs-linenum>202: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>((State# a) -&gt; ((State# a), {x7 : (MArray a) | ((maLen x7) == n)}))
-&gt; (ST a {x3 : (MArray a) | ((maLen x3) == n)})</span><span class='hs-conid'>ST</span></a> <a class=annot href="#"><span class=annottext>(((State# a)
  -&gt; ((State# a), {x17 : (MArray a) | ((maLen x17) == n)}))
 -&gt; (ST a {x12 : (MArray a) | ((maLen x12) == n)}))
-&gt; ((State# a)
    -&gt; ((State# a), {x17 : (MArray a) | ((maLen x17) == n)}))
-&gt; (ST a {x12 : (MArray a) | ((maLen x12) == n)})</span><span class='hs-varop'>$</span></a> <span class='hs-keyglyph'>\</span><a class=annot href="#"><span class=annottext>(State# a)</span><span class='hs-varid'>s1</span></a><span class='hs-cpp'>#</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>203: </span>       <span class='hs-keyword'>case</span> <a class=annot href="#"><span class=annottext>Int# -&gt; (State# a) -&gt; ((State# a), (MutableByteArray# a))</span><span class='hs-varid'>newByteArray</span></a><span class='hs-cpp'>#</span> <a class=annot href="#"><span class=annottext>{x2 : Int# | (x2 == len)}</span><span class='hs-varid'>len</span></a><span class='hs-cpp'>#</span> <a class=annot href="#"><span class=annottext>{x2 : (State# a) | (x2 == s1)}</span><span class='hs-varid'>s1</span></a><span class='hs-cpp'>#</span> <span class='hs-keyword'>of</span>
<span class=hs-linenum>204: </span>         <span class='hs-layout'>(</span><span class='hs-cpp'>#</span> <span class='hs-varid'>s2</span><span class='hs-cpp'>#</span><span class='hs-layout'>,</span> <span class='hs-varid'>marr</span><span class='hs-cpp'>#</span> <span class='hs-cpp'>#</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>forall a b. a -&gt; b -&gt; (a, b)</span><span class='hs-layout'>(</span></a><span class='hs-cpp'>#</span> <a class=annot href="#"><span class=annottext>{x2 : (State# a) | (x2 == s2)}</span><span class='hs-varid'>s2</span></a><span class='hs-cpp'>#</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>x1:(MutableByteArray# a)
-&gt; x2:{x5 : Int | (x5 &gt;= 0)}
-&gt; {x3 : (MArray a) | ((maBA x3) == x1) &amp;&amp; ((maLen x3) == x2)}</span><span class='hs-conid'>MArray</span></a> <a class=annot href="#"><span class=annottext>{x2 : (MutableByteArray# a) | (x2 == marr)}</span><span class='hs-varid'>marr</span></a><span class='hs-cpp'>#</span> <a class=annot href="#"><span class=annottext>{x3 : Int | (x3 == n) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>n</span></a> <span class='hs-cpp'>#</span><span class='hs-layout'>)</span>
<span class=hs-linenum>205: </span>  <span class='hs-keyword'>where</span> <span class='hs-varop'>!</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span><span class='hs-cpp'>#</span> <span class='hs-varid'>len</span><span class='hs-cpp'>#</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x11 : Int | (x11 == n) &amp;&amp; (x11 &gt;= 0)}
-&gt; {x8 : Int | ((x1 == 1) =&gt; (x8 == (x1 * 2))) &amp;&amp; ((x1 == 1) =&gt; (x8 == (n * 2))) &amp;&amp; ((n == 1) =&gt; (x8 == (x1 * 2))) &amp;&amp; ((n == 1) =&gt; (x8 == (n * 2))) &amp;&amp; (x8 &gt;= 0) &amp;&amp; (x8 &gt;= x1) &amp;&amp; (x8 &gt;= n)}</span><span class='hs-varid'>bytesInArray</span></a> <a class=annot href="#"><span class=annottext>{x3 : Int | (x3 == n) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>n</span></a>
<span class=hs-linenum>206: </span>        <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>highBit</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>maxBound</span></a> <a class=annot href="#"><span class=annottext>Int -&gt; Int -&gt; Int</span><span class='hs-varop'>`xor`</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>maxBound</span></a> <a class=annot href="#"><span class=annottext>Int -&gt; Int -&gt; Int</span><span class='hs-varop'>`shiftR`</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>207: </span>        <a class=annot href="#"><span class=annottext>n:{VV : Int | (VV == n) &amp;&amp; (VV &gt;= 0)}
-&gt; {VV : Int | ((n == 1) =&gt; (VV == (n * 2))) &amp;&amp; ((n == 1) =&gt; (VV == (n * 2))) &amp;&amp; ((n == 1) =&gt; (VV == (n * 2))) &amp;&amp; ((n == 1) =&gt; (VV == (n * 2))) &amp;&amp; (VV &gt;= 0) &amp;&amp; (VV &gt;= n) &amp;&amp; (VV &gt;= n)}</span><span class='hs-varid'>bytesInArray</span></a> <a class=annot href="#"><span class=annottext>{VV : Int | (VV == n) &amp;&amp; (VV &gt;= 0)}</span><span class='hs-varid'>n</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x4 : Int | (x4 == n) &amp;&amp; (x4 == n) &amp;&amp; (x4 &gt;= 0)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:{x7 : Int | (x7 &gt;= 0)}
-&gt; x2:{x5 : Int | (x5 &gt;= 0)}
-&gt; {x3 : Int | ((x2 == 1) =&gt; (x3 == (x1 * 2))) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varop'>`shiftL`</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a>
</pre>

`new n` is an `ST` action that produces an `MArray s` with `n` slots each 
of which is 2 bytes (as internally `text` manipulates `Word16`s).

The verification process here is quite simple; LH recognizes that 
the `n` used to construct the returned array (`MArray marr# n`) 
the same `n` passed to `new`. 

Writing into an `MArray`
------------------------

Once we have *created* an `MArray`, we'll want to write our data into it. 

A `Nat` is a valid index into an `MArray` if it is *strictly less than* 
the size of the array.


<pre><span class=hs-linenum>226: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>MAValidI</span> <span class='hs-conid'>MA</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&lt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>maLen</span> <span class='hs-conid'>MA</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

We use this valid index alias to refine the type of `unsafeWrite`


<pre><span class=hs-linenum>232: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>unsafeWrite</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>ma</span><span class='hs-conop'>:</span><span class='hs-conid'>MArray</span> <span class='hs-varid'>s</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>MAValidI</span> <span class='hs-varid'>ma</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Word16</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>ST</span> <span class='hs-varid'>s</span> <span class='hs-conid'>()</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>233: </span><a class=annot href="#"><span class=annottext>forall a.
x1:(MArray a)
-&gt; {v : Int | (v &gt;= 0) &amp;&amp; (v &lt; (maLen x1))} -&gt; Word16 -&gt; (ST a ())</span><span class='hs-definition'>unsafeWrite</span></a> <span class='hs-conid'>MArray</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>..</span><span class='hs-layout'>}</span> <a class=annot href="#"><span class=annottext>{v : Int | (v &gt;= 0)}</span><span class='hs-varid'>i</span></a><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span><span class='hs-cpp'>#</span> <span class='hs-varid'>i</span><span class='hs-cpp'>#</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-conid'>W16</span><span class='hs-cpp'>#</span> <span class='hs-varid'>e</span><span class='hs-cpp'>#</span><span class='hs-layout'>)</span>
<span class=hs-linenum>234: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x5 : Int | (x5 == i) &amp;&amp; (x5 == i) &amp;&amp; (x5 == (i  :  int)) &amp;&amp; (x5 &gt;= 0)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x1:Bool
-&gt; x2:Bool
-&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (((Prop x1)) || ((Prop x2))))}</span><span class='hs-varop'>||</span></a> <a class=annot href="#"><span class=annottext>{x5 : Int | (x5 == i) &amp;&amp; (x5 == i) &amp;&amp; (x5 == (i  :  int)) &amp;&amp; (x5 &gt;= 0)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 &gt;= x2))}</span><span class='hs-varop'>&gt;=</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 &gt;= 0)}</span><span class='hs-varid'>maLen</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x6 : Bool | ((Prop x6))} -&gt; (ST a ()) -&gt; (ST a ())</span><span class='hs-varid'>assert</span></a> <a class=annot href="#"><span class=annottext>{x3 : Bool | (not (((Prop x3)))) &amp;&amp; (x3 == GHC.Types.False)}</span><span class='hs-conid'>False</span></a> <a class=annot href="#"><span class=annottext>((ST a ()) -&gt; (ST a ())) -&gt; (ST a ()) -&gt; (ST a ())</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>[Char] -&gt; (ST a ())</span><span class='hs-varid'>error</span></a> <a class=annot href="#"><span class=annottext>{x2 : [Char] | ((len x2) &gt;= 0)}</span><span class='hs-str'>"out of bounds"</span></a>
<span class=hs-linenum>235: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>((State# a) -&gt; ((State# a), ())) -&gt; (ST a ())</span><span class='hs-conid'>ST</span></a> <a class=annot href="#"><span class=annottext>(((State# a) -&gt; ((State# a), ())) -&gt; (ST a ()))
-&gt; ((State# a) -&gt; ((State# a), ())) -&gt; (ST a ())</span><span class='hs-varop'>$</span></a> <span class='hs-keyglyph'>\</span><a class=annot href="#"><span class=annottext>(State# a)</span><span class='hs-varid'>s1</span></a><span class='hs-cpp'>#</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>236: </span>      <span class='hs-keyword'>case</span> <a class=annot href="#"><span class=annottext>(MutableByteArray# a) -&gt; Int# -&gt; Word# -&gt; (State# a) -&gt; (State# a)</span><span class='hs-varid'>writeWord16Array</span></a><span class='hs-cpp'>#</span> <a class=annot href="#"><span class=annottext>(MutableByteArray# a)</span><span class='hs-varid'>maBA</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int# | (x2 == i)}</span><span class='hs-varid'>i</span></a><span class='hs-cpp'>#</span> <a class=annot href="#"><span class=annottext>{x2 : Word# | (x2 == e)}</span><span class='hs-varid'>e</span></a><span class='hs-cpp'>#</span> <a class=annot href="#"><span class=annottext>{x2 : (State# a) | (x2 == s1)}</span><span class='hs-varid'>s1</span></a><span class='hs-cpp'>#</span> <span class='hs-keyword'>of</span>
<span class=hs-linenum>237: </span>        <span class='hs-varid'>s2</span><span class='hs-cpp'>#</span> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>forall a b. a -&gt; b -&gt; (a, b)</span><span class='hs-layout'>(</span></a><span class='hs-cpp'>#</span> <a class=annot href="#"><span class=annottext>(State# a)</span><span class='hs-varid'>s2</span></a><span class='hs-cpp'>#</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{x2 : () | (x2 == GHC.Tuple.())}</span><span class='hs-conid'>()</span></a> <span class='hs-cpp'>#</span><span class='hs-layout'>)</span>
</pre>

Note that, when compiled with appropriate options, the implementation of
`text` checks the bounds at run-time. However, LiquidHaskell can statically
prove that the error branch is unreachable, i.e. the `assert` **cannot fail**
(as long as the inputs adhere to the given specification) by giving `assert`
the type:


<pre><span class=hs-linenum>247: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>assert</span> <span class='hs-varid'>assert</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Bool</span> <span class='hs-keyword'>| (Prop v)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
</pre>

Bulk Writing into an `MArray`
-----------------------------

So now we can write individual `Word16`s into an array, but maybe we
have a whole bunch of text we want to dump into the array. Remember,
`text` is supposed to be fast! C has `memcpy` for cases like this but 
it's notoriously unsafe; with the right type however, we can regain safety. 
`text` provides a wrapper around `memcpy` to copy `n` elements from 
one `MArray` to another.

`copyM` requires two `MArray`s and valid offsets into each -- note
that a valid offset is **not** necessarily a valid *index*, it may
be one element out-of-bounds


<pre><span class=hs-linenum>265: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>MAValidO</span> <span class='hs-conid'>MA</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&lt;=</span> <span class='hs-layout'>(</span><span class='hs-varid'>maLen</span> <span class='hs-conid'>MA</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

-- and a `count` of elements to copy.
The `count` must represent a valid region in each `MArray`, in
other words `offset + count <= length` must hold for each array.


<pre><span class=hs-linenum>273: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>copyM</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>dest</span><span class='hs-conop'>:</span><span class='hs-conid'>MArray</span> <span class='hs-varid'>s</span>
<span class=hs-linenum>274: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>didx</span><span class='hs-conop'>:</span><span class='hs-conid'>MAValidO</span> <span class='hs-varid'>dest</span>
<span class=hs-linenum>275: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>src</span><span class='hs-conop'>:</span><span class='hs-conid'>MArray</span> <span class='hs-varid'>s</span>
<span class=hs-linenum>276: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>sidx</span><span class='hs-conop'>:</span><span class='hs-conid'>MAValidO</span> <span class='hs-varid'>src</span>
<span class=hs-linenum>277: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| (((didx + v) &lt;= (maLen dest))
                    &amp;&amp; ((sidx + v) &lt;= (maLen src)))}</span>
<span class=hs-linenum>279: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>ST</span> <span class='hs-varid'>s</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>280: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>281: </span><a class=annot href="#"><span class=annottext>forall a.
x1:(MArray a)
-&gt; x2:{v : Int | (v &gt;= 0) &amp;&amp; (v &lt;= (maLen x1))}
-&gt; x3:(MArray a)
-&gt; x4:{v : Int | (v &gt;= 0) &amp;&amp; (v &lt;= (maLen x3))}
-&gt; {v : Int | (v &gt;= 0) &amp;&amp; ((x2 + v) &lt;= (maLen x1)) &amp;&amp; ((x4 + v) &lt;= (maLen x3))}
-&gt; (ST a ())</span><span class='hs-definition'>copyM</span></a> <a class=annot href="#"><span class=annottext>(MArray a)</span><span class='hs-varid'>dest</span></a> <a class=annot href="#"><span class=annottext>{v : Int | (v &gt;= 0) &amp;&amp; (v &lt;= (maLen dest))}</span><span class='hs-varid'>didx</span></a> <a class=annot href="#"><span class=annottext>(MArray a)</span><span class='hs-varid'>src</span></a> <a class=annot href="#"><span class=annottext>{v : Int | (v &gt;= 0) &amp;&amp; (v &lt;= (maLen src))}</span><span class='hs-varid'>sidx</span></a> <a class=annot href="#"><span class=annottext>{v : Int | (v &gt;= 0) &amp;&amp; ((didx + v) &lt;= (maLen dest)) &amp;&amp; ((sidx + v) &lt;= (maLen src))}</span><span class='hs-varid'>count</span></a>
<span class=hs-linenum>282: </span>    <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x5 : Int | (x5 == count) &amp;&amp; (x5 &gt;= 0) &amp;&amp; ((didx + x5) &lt;= (maLen dest)) &amp;&amp; ((sidx + x5) &lt;= (maLen src))}</span><span class='hs-varid'>count</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 &lt;= x2))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>() -&gt; (ST a ())</span><span class='hs-varid'>return</span></a> <a class=annot href="#"><span class=annottext>{x2 : () | (x2 == GHC.Tuple.())}</span><span class='hs-conid'>()</span></a>
<span class=hs-linenum>283: </span>    <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span>
<span class=hs-linenum>284: </span>    <a class=annot href="#"><span class=annottext>{x6 : Bool | ((Prop x6))} -&gt; (ST a ()) -&gt; (ST a ())</span><span class='hs-varid'>assert</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x4 : Int | (x4 == sidx) &amp;&amp; (x4 &gt;= 0) &amp;&amp; (x4 &lt;= (maLen src))}</span><span class='hs-varid'>sidx</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x4 : Int | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{x5 : Int | (x5 == count) &amp;&amp; (x5 &gt;= 0) &amp;&amp; ((didx + x5) &lt;= (maLen dest)) &amp;&amp; ((sidx + x5) &lt;= (maLen src))}</span><span class='hs-varid'>count</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 &lt;= x2))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>x1:(MArray a) -&gt; {x3 : Int | (x3 == (maLen x1)) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>maLen</span></a> <a class=annot href="#"><span class=annottext>{x2 : (MArray a) | (x2 == src)}</span><span class='hs-varid'>src</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>((ST a ()) -&gt; (ST a ()))
-&gt; ((IO ()) -&gt; (ST a ()))
-&gt; (IO ())
-&gt; exists [(ST a ())].(ST a ())</span><span class='hs-varop'>.</span></a>
<span class=hs-linenum>285: </span>    <a class=annot href="#"><span class=annottext>{x6 : Bool | ((Prop x6))} -&gt; (ST a ()) -&gt; (ST a ())</span><span class='hs-varid'>assert</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x4 : Int | (x4 == didx) &amp;&amp; (x4 &gt;= 0) &amp;&amp; (x4 &lt;= (maLen dest))}</span><span class='hs-varid'>didx</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x4 : Int | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{x5 : Int | (x5 == count) &amp;&amp; (x5 &gt;= 0) &amp;&amp; ((didx + x5) &lt;= (maLen dest)) &amp;&amp; ((sidx + x5) &lt;= (maLen src))}</span><span class='hs-varid'>count</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 &lt;= x2))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>x1:(MArray a) -&gt; {x3 : Int | (x3 == (maLen x1)) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>maLen</span></a> <a class=annot href="#"><span class=annottext>{x2 : (MArray a) | (x2 == dest)}</span><span class='hs-varid'>dest</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>((ST a ()) -&gt; (ST a ()))
-&gt; ((IO ()) -&gt; (ST a ()))
-&gt; (IO ())
-&gt; exists [(ST a ())].(ST a ())</span><span class='hs-varop'>.</span></a>
<span class=hs-linenum>286: </span>    <a class=annot href="#"><span class=annottext>(IO ()) -&gt; (ST a ())</span><span class='hs-varid'>unsafeIOToST</span></a> <a class=annot href="#"><span class=annottext>((IO ()) -&gt; (ST a ())) -&gt; (IO ()) -&gt; (ST a ())</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>(MutableByteArray# a)
-&gt; CSize -&gt; (MutableByteArray# a) -&gt; CSize -&gt; CSize -&gt; (IO ())</span><span class='hs-varid'>memcpyM</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(MArray a) -&gt; (MutableByteArray# a)</span><span class='hs-varid'>maBA</span></a> <a class=annot href="#"><span class=annottext>{x2 : (MArray a) | (x2 == dest)}</span><span class='hs-varid'>dest</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:Int -&gt; {x2 : CSize | (x2 == x1)}</span><span class='hs-varid'>fromIntegral</span></a> <a class=annot href="#"><span class=annottext>{x4 : Int | (x4 == didx) &amp;&amp; (x4 &gt;= 0) &amp;&amp; (x4 &lt;= (maLen dest))}</span><span class='hs-varid'>didx</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>287: </span>                           <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(MArray a) -&gt; (MutableByteArray# a)</span><span class='hs-varid'>maBA</span></a> <a class=annot href="#"><span class=annottext>{x2 : (MArray a) | (x2 == src)}</span><span class='hs-varid'>src</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:Int -&gt; {x2 : CSize | (x2 == x1)}</span><span class='hs-varid'>fromIntegral</span></a> <a class=annot href="#"><span class=annottext>{x4 : Int | (x4 == sidx) &amp;&amp; (x4 &gt;= 0) &amp;&amp; (x4 &lt;= (maLen src))}</span><span class='hs-varid'>sidx</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>288: </span>                           <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:Int -&gt; {x2 : CSize | (x2 == x1)}</span><span class='hs-varid'>fromIntegral</span></a> <a class=annot href="#"><span class=annottext>{x5 : Int | (x5 == count) &amp;&amp; (x5 &gt;= 0) &amp;&amp; ((didx + x5) &lt;= (maLen dest)) &amp;&amp; ((sidx + x5) &lt;= (maLen src))}</span><span class='hs-varid'>count</span></a><span class='hs-layout'>)</span>
</pre>

Again, the two `assert`s in the function were in the original code as 
(optionally compiled out) run-time checks of the precondition, but with 
LiquidHaskell we can actually *prove* that the `assert`s **always succeed**.

Freezing an `MArray` into an `Array`
------------------------------------

Before we can package up our `MArray` into a `Text`, we need to
*freeze* it, preventing any further mutation. The key property 
here is of course that the frozen `Array` should have the same 
length as the `MArray`.

Just as `MArray` wraps a mutable array, `Array` wraps an *immutable*
`ByteArray#` and carries its length in `Word16`s.


<pre><span class=hs-linenum>307: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>Array</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Array</span> <span class='hs-layout'>{</span> <a class=annot href="#"><span class=annottext>Array -&gt; ByteArray#</span><span class='hs-varid'>aBA</span></a>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>ByteArray</span><span class='hs-cpp'>#</span>
<span class=hs-linenum>308: </span>                   <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>x1:Array -&gt; {v : Int | (v == (aLen x1)) &amp;&amp; (v &gt;= 0)}</span><span class='hs-varid'>aLen</span></a> <span class='hs-keyglyph'>::</span> <span class='hs-varop'>!</span><span class='hs-conid'>Int</span>
<span class=hs-linenum>309: </span>                   <span class='hs-layout'>}</span>
</pre>

As before, we get free accessor measures `aBA` and `aLen` just by
refining the data definition


<pre><span class=hs-linenum>316: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>Array</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Array</span> <span class='hs-layout'>{</span> <span class='hs-varid'>aBA</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>ByteArray</span><span class='hs-cpp'>#</span>
<span class=hs-linenum>317: </span>                       <span class='hs-layout'>,</span> <span class='hs-varid'>aLen</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Nat</span>
<span class=hs-linenum>318: </span>                       <span class='hs-layout'>}</span>
<span class=hs-linenum>319: </span>  <span class='hs-keyword'>@-}</span>
</pre>

so we can refer to the components of an `Array` in our refinements.
Using these measures, we can define


<pre><span class=hs-linenum>326: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>ArrayN</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Array</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>aLen</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>327: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>unsafeFreeze</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>ma</span><span class='hs-conop'>:</span><span class='hs-conid'>MArray</span> <span class='hs-varid'>s</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>ST</span> <span class='hs-varid'>s</span> <span class='hs-layout'>(</span><span class='hs-conid'>ArrayN</span> <span class='hs-layout'>(</span><span class='hs-varid'>maLen</span> <span class='hs-varid'>ma</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>328: </span><a class=annot href="#"><span class=annottext>forall a.
x1:(MArray a) -&gt; (ST a {v : Array | ((aLen v) == (maLen x1))})</span><span class='hs-definition'>unsafeFreeze</span></a> <span class='hs-conid'>MArray</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>..</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>((State# a) -&gt; ((State# a), {x5 : Array | false}))
-&gt; (ST a {x2 : Array | false})</span><span class='hs-conid'>ST</span></a> <a class=annot href="#"><span class=annottext>(((State# a)
  -&gt; {x11 : ((State# a), {x13 : Array | false}) | false})
 -&gt; (ST a {x9 : Array | false}))
-&gt; ((State# a)
    -&gt; {x11 : ((State# a), {x13 : Array | false}) | false})
-&gt; (ST a {x9 : Array | false})</span><span class='hs-varop'>$</span></a> <span class='hs-keyglyph'>\</span><a class=annot href="#"><span class=annottext>(State# a)</span><span class='hs-varid'>s</span></a><span class='hs-cpp'>#</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>329: </span>                          <a class=annot href="#"><span class=annottext>forall a b. a -&gt; b -&gt; (a, b)</span><span class='hs-layout'>(</span></a><span class='hs-cpp'>#</span> <a class=annot href="#"><span class=annottext>{x2 : (State# a) | (x2 == s)}</span><span class='hs-varid'>s</span></a><span class='hs-cpp'>#</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>x1:ByteArray#
-&gt; x2:{x5 : Int | (x5 &gt;= 0)}
-&gt; {x3 : Array | ((aBA x3) == x1) &amp;&amp; ((aLen x3) == x2)}</span><span class='hs-conid'>Array</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(MutableByteArray# a) -&gt; {x1 : ByteArray# | false}</span><span class='hs-varid'>unsafeCoerce</span></a><span class='hs-cpp'>#</span> <a class=annot href="#"><span class=annottext>(MutableByteArray# a)</span><span class='hs-varid'>maBA</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 &gt;= 0)}</span><span class='hs-varid'>maLen</span></a> <span class='hs-cpp'>#</span><span class='hs-layout'>)</span>
</pre>

Again, LiquidHaskell is happy to prove our specification as we simply
copy the length parameter `maLen` over into the `Array`.

Reading from an `Array`
------------------------
Finally, we will eventually want to read a value out of the
`Array`. As with `unsafeWrite` we require a valid index into the
`Array`, which we denote using the `AValidI` alias.


<pre><span class=hs-linenum>342: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>AValidI</span> <span class='hs-conid'>A</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&lt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>aLen</span> <span class='hs-conid'>A</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>343: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>unsafeIndex</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-conop'>:</span><span class='hs-conid'>Array</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>AValidI</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Word16</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>344: </span><a class=annot href="#"><span class=annottext>x1:Array -&gt; {v : Int | (v &gt;= 0) &amp;&amp; (v &lt; (aLen x1))} -&gt; Word16</span><span class='hs-definition'>unsafeIndex</span></a> <span class='hs-conid'>Array</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>..</span><span class='hs-layout'>}</span> <a class=annot href="#"><span class=annottext>{v : Int | (v &gt;= 0)}</span><span class='hs-varid'>i</span></a><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span><span class='hs-cpp'>#</span> <span class='hs-varid'>i</span><span class='hs-cpp'>#</span><span class='hs-layout'>)</span>
<span class=hs-linenum>345: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x5 : Int | (x5 == i) &amp;&amp; (x5 == i) &amp;&amp; (x5 == (i  :  int)) &amp;&amp; (x5 &gt;= 0)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x1:Bool
-&gt; x2:Bool
-&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (((Prop x1)) || ((Prop x2))))}</span><span class='hs-varop'>||</span></a> <a class=annot href="#"><span class=annottext>{x5 : Int | (x5 == i) &amp;&amp; (x5 == i) &amp;&amp; (x5 == (i  :  int)) &amp;&amp; (x5 &gt;= 0)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 &gt;= x2))}</span><span class='hs-varop'>&gt;=</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 &gt;= 0)}</span><span class='hs-varid'>aLen</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x4 : Bool | ((Prop x4))} -&gt; Word16 -&gt; Word16</span><span class='hs-varid'>assert</span></a> <a class=annot href="#"><span class=annottext>{x3 : Bool | (not (((Prop x3)))) &amp;&amp; (x3 == GHC.Types.False)}</span><span class='hs-conid'>False</span></a> <a class=annot href="#"><span class=annottext>(Word16 -&gt; Word16) -&gt; Word16 -&gt; Word16</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>[Char] -&gt; Word16</span><span class='hs-varid'>error</span></a> <a class=annot href="#"><span class=annottext>{x2 : [Char] | ((len x2) &gt;= 0)}</span><span class='hs-str'>"out of bounds"</span></a>
<span class=hs-linenum>346: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>case</span> <a class=annot href="#"><span class=annottext>ByteArray# -&gt; Int# -&gt; Word#</span><span class='hs-varid'>indexWord16Array</span></a><span class='hs-cpp'>#</span> <a class=annot href="#"><span class=annottext>ByteArray#</span><span class='hs-varid'>aBA</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int# | (x2 == i)}</span><span class='hs-varid'>i</span></a><span class='hs-cpp'>#</span> <span class='hs-keyword'>of</span>
<span class=hs-linenum>347: </span>                  <span class='hs-varid'>r</span><span class='hs-cpp'>#</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>Word# -&gt; Word16</span><span class='hs-conid'>W16</span></a><span class='hs-cpp'>#</span> <a class=annot href="#"><span class=annottext>Word#</span><span class='hs-varid'>r</span></a><span class='hs-cpp'>#</span><span class='hs-layout'>)</span>
</pre>

As before, LiquidHaskell can easily prove that the error branch
is unreachable, i.e. is *never* executed at run-time.

Wrapping it all up
------------------

Now we can finally define the core datatype of the `text` package!
A `Text` value consists of three fields:

A. an `Array`,

B. an `Int` offset into the *middle* of the array, and

C. an `Int` length denoting the number of valid indices *after* the offset.

We can specify the invariants for fields (b) and (c) with the refined type:


<pre><span class=hs-linenum>368: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>Text</span>
<span class=hs-linenum>369: </span>      <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Text</span> <span class='hs-layout'>{</span> <span class='hs-varid'>tArr</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Array</span>
<span class=hs-linenum>370: </span>             <span class='hs-layout'>,</span> <span class='hs-varid'>tOff</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span>      <span class='hs-varop'>&lt;=</span> <span class='hs-layout'>(</span><span class='hs-varid'>aLen</span> <span class='hs-varid'>tArr</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>371: </span>             <span class='hs-layout'>,</span> <span class='hs-varid'>tLen</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span><span class='hs-varop'>+</span><span class='hs-varid'>tOff</span> <span class='hs-varop'>&lt;=</span> <span class='hs-layout'>(</span><span class='hs-varid'>aLen</span> <span class='hs-varid'>tArr</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>372: </span>             <span class='hs-layout'>}</span>
<span class=hs-linenum>373: </span>  <span class='hs-keyword'>@-}</span>
</pre>

These invariants ensure that any *index* we pick between `tOff` and
`tOff + tLen` will be a valid index into `tArr`. 

As shown above with `new`, `unsafeWrite`, and `unsafeFreeze`, we can type the
top-level function that creates a `Text` from a `[Char]` as:


<pre><span class=hs-linenum>383: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>pack</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>s</span><span class='hs-conop'>:</span><span class='hs-conid'>String</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Text</span> <span class='hs-keyword'>| (tLen v) = (len s)}</span> <span class='hs-keyword'>@-}</span>
</pre>

Preventing Bleeds
-----------------

Now, let us close the circle and return to potentially *bleeding* function:


<pre><span class=hs-linenum>392: </span><a class=annot href="#"><span class=annottext>Text -&gt; Int -&gt; Char</span><span class='hs-definition'>charAt'</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Text</span> <span class='hs-varid'>a</span> <span class='hs-varid'>o</span> <span class='hs-varid'>l</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>Word16 -&gt; exists [Int].Char</span><span class='hs-varid'>word2char</span></a> <a class=annot href="#"><span class=annottext>(Word16 -&gt; Char) -&gt; Word16 -&gt; Char</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>x1:Array -&gt; {x4 : Int | (x4 &gt;= 0) &amp;&amp; (x4 &lt; (aLen x1))} -&gt; Word16</span><span class='hs-varid'>unsafeIndex</span></a> <a class=annot href="#"><span class=annottext>{x2 : Array | (x2 == a)}</span><span class='hs-varid'>a</span></a> <span class='hs-layout'>(</span><span class=hs-error><a class=annot href="#"><span class=annottext>{x4 : Int | (x4 == o) &amp;&amp; (x4 &gt;= 0) &amp;&amp; (x4 &lt;= (aLen a))}</span><span class='hs-varid'>o</span></a></span><span class=hs-error><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x4 : Int | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a></span><span class=hs-error><a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == i)}</span><span class='hs-varid'>i</span></a></span><span class='hs-layout'>)</span>
<span class=hs-linenum>393: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>394: </span>    <a class=annot href="#"><span class=annottext>Word16 -&gt; exists [Int].Char</span><span class='hs-varid'>word2char</span></a>          <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>Int -&gt; Char</span><span class='hs-varid'>chr</span></a> <a class=annot href="#"><span class=annottext>(Int -&gt; Char) -&gt; (Word16 -&gt; Int) -&gt; Word16 -&gt; exists [Int].Char</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>x1:Word16 -&gt; {x2 : Int | (x2 == x1)}</span><span class='hs-varid'>fromIntegral</span></a>
</pre>

Aha! LiquidHaskell flags the call to `unsafeIndex` because of course, `i` may fall
outside the bounds of the given array `a`! We can remedy that by specifying
a bound for the index:


<pre><span class=hs-linenum>402: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>charAt</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>t</span><span class='hs-conop'>:</span><span class='hs-conid'>Text</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| v &lt; (tLen t)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Char</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>403: </span><a class=annot href="#"><span class=annottext>x1:Text -&gt; {v : Int | (v &gt;= 0) &amp;&amp; (v &lt; (tLen x1))} -&gt; Char</span><span class='hs-definition'>charAt</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Text</span> <span class='hs-varid'>a</span> <span class='hs-varid'>o</span> <span class='hs-varid'>l</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{v : Int | (v &gt;= 0)}</span><span class='hs-varid'>i</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>Word16 -&gt; exists [Int].Char</span><span class='hs-varid'>word2char</span></a> <a class=annot href="#"><span class=annottext>(Word16 -&gt; Char) -&gt; Word16 -&gt; Char</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>x1:Array -&gt; {x4 : Int | (x4 &gt;= 0) &amp;&amp; (x4 &lt; (aLen x1))} -&gt; Word16</span><span class='hs-varid'>unsafeIndex</span></a> <a class=annot href="#"><span class=annottext>{x2 : Array | (x2 == a)}</span><span class='hs-varid'>a</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x4 : Int | (x4 == o) &amp;&amp; (x4 &gt;= 0) &amp;&amp; (x4 &lt;= (aLen a))}</span><span class='hs-varid'>o</span></a><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x4 : Int | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a><a class=annot href="#"><span class=annottext>{x3 : Int | (x3 == i) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>404: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>405: </span>    <a class=annot href="#"><span class=annottext>Word16 -&gt; exists [Int].Char</span><span class='hs-varid'>word2char</span></a>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>Int -&gt; Char</span><span class='hs-varid'>chr</span></a> <a class=annot href="#"><span class=annottext>(Int -&gt; Char) -&gt; (Word16 -&gt; Int) -&gt; Word16 -&gt; exists [Int].Char</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>x1:Word16 -&gt; {x2 : Int | (x2 == x1)}</span><span class='hs-varid'>fromIntegral</span></a>
</pre>

That is, we can access the `i`th `Char` as long as `i` is a `Nat` less
than the the size of the text, namely `tLen t`. Now LiquidHaskell is convinced
that the call to `unsafeIndex` is safe, but of course, we have passed
the burden of proof onto users of `charAt`.

Now, if we try calling `charAt` as we did at the beginning


<pre><span class=hs-linenum>416: </span><a class=annot href="#"><span class=annottext>[Char]</span><span class='hs-definition'>test</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x3 : [Char] | (((null x3)) &lt;=&gt; false) &amp;&amp; ((len x3) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{x2 : Char | (x2 == good)}</span><span class='hs-varid'>good</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{x2 : Char | (x2 == bad)}</span><span class='hs-varid'>bad</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>417: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>418: </span>    <a class=annot href="#"><span class=annottext>{x2 : [Char] | (((null x2)) &lt;=&gt; false)}</span><span class='hs-varid'>dog</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : [Char] | (((null x2)) &lt;=&gt; false)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>Char</span><span class='hs-chr'>'d'</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>Char</span><span class='hs-chr'>'o'</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>Char</span><span class='hs-chr'>'g'</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>419: </span>    <a class=annot href="#"><span class=annottext>Char</span><span class='hs-varid'>good</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:Text -&gt; {x4 : Int | (x4 &gt;= 0) &amp;&amp; (x4 &lt; (tLen x1))} -&gt; Char</span><span class='hs-varid'>charAt</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:[Char] -&gt; {x2 : Text | ((tLen x2) == (len x1))}</span><span class='hs-varid'>pack</span></a> <a class=annot href="#"><span class=annottext>{x4 : [Char] | (((null x4)) &lt;=&gt; false) &amp;&amp; (x4 == dog) &amp;&amp; ((len x4) &gt;= 0)}</span><span class='hs-varid'>dog</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (2  :  int))}</span><span class='hs-num'>2</span></a>
<span class=hs-linenum>420: </span>    <a class=annot href="#"><span class=annottext>Char</span><span class='hs-varid'>bad</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:Text -&gt; {x4 : Int | (x4 &gt;= 0) &amp;&amp; (x4 &lt; (tLen x1))} -&gt; Char</span><span class='hs-varid'>charAt</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:[Char] -&gt; {x2 : Text | ((tLen x2) == (len x1))}</span><span class='hs-varid'>pack</span></a> <a class=annot href="#"><span class=annottext>{x4 : [Char] | (((null x4)) &lt;=&gt; false) &amp;&amp; (x4 == dog) &amp;&amp; ((len x4) &gt;= 0)}</span><span class='hs-varid'>dog</span></a><span class='hs-layout'>)</span> <span class=hs-error><a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (3  :  int))}</span><span class='hs-num'>3</span></a></span>
</pre>

we see that LiquidHaskell verifies the `good` call, but flags `bad` as
**unsafe**.

Enforcing Sanitization
----------------------

EDIT: As several folks have pointed out, the #heartbleed error was
due to inputs not being properly sanitized. The above approach 
**ensures, at compile time**, that proper sanitization has been 
performed. 

To see this in action, lets write a little function that just shows the 
character at a given position:


<pre><span class=hs-linenum>438: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>showCharAt</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>t</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| v &lt; (tLen t)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>_</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>439: </span><a class=annot href="#"><span class=annottext>x1:Text -&gt; {v : Int | (v &gt;= 0) &amp;&amp; (v &lt; (tLen x1))} -&gt; (IO ())</span><span class='hs-definition'>showCharAt</span></a> <a class=annot href="#"><span class=annottext>Text</span><span class='hs-varid'>t</span></a> <a class=annot href="#"><span class=annottext>{v : Int | (v &gt;= 0) &amp;&amp; (v &lt; (tLen t))}</span><span class='hs-varid'>i</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[Char] -&gt; (IO ())</span><span class='hs-varid'>putStrLn</span></a> <a class=annot href="#"><span class=annottext>([Char] -&gt; (IO ())) -&gt; [Char] -&gt; (IO ())</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>Char -&gt; [Char]</span><span class='hs-varid'>show</span></a> <a class=annot href="#"><span class=annottext>(Char -&gt; [Char]) -&gt; Char -&gt; [Char]</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>x1:Text -&gt; {x4 : Int | (x4 &gt;= 0) &amp;&amp; (x4 &lt; (tLen x1))} -&gt; Char</span><span class='hs-varid'>charAt</span></a> <a class=annot href="#"><span class=annottext>{x2 : Text | (x2 == t)}</span><span class='hs-varid'>t</span></a> <a class=annot href="#"><span class=annottext>{x4 : Int | (x4 == i) &amp;&amp; (x4 &gt;= 0) &amp;&amp; (x4 &lt; (tLen t))}</span><span class='hs-varid'>i</span></a>
</pre>

Now, the following function, that correctly sanitizes is **accepted**


<pre><span class=hs-linenum>445: </span><span class='hs-definition'>goodMain</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>IO</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>446: </span><a class=annot href="#"><span class=annottext>(IO ())</span><span class='hs-definition'>goodMain</span></a> 
<span class=hs-linenum>447: </span>  <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>do</span> <a class=annot href="#"><span class=annottext>Text</span><span class='hs-varid'>txt</span></a> <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>x1:[Char] -&gt; {x2 : Text | ((tLen x2) == (len x1))}</span><span class='hs-varid'>pack</span></a> <a class=annot href="#"><span class=annottext>([Char] -&gt; Text) -&gt; (IO [Char]) -&gt; (IO Text)</span><span class='hs-varop'>&lt;$&gt;</span></a> <a class=annot href="#"><span class=annottext>{x2 : (IO [Char]) | (x2 == System.IO.getLine)}</span><span class='hs-varid'>getLine</span></a>
<span class=hs-linenum>448: </span>       <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i</span></a>   <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>(IO Int)</span><span class='hs-varid'>readLn</span></a>
<span class=hs-linenum>449: </span>       <span class='hs-keyword'>if</span> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 &lt;= x2))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == i)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Bool
-&gt; x2:Bool
-&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (((Prop x1)) &amp;&amp; ((Prop x2))))}</span><span class='hs-varop'>&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == i)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>x1:Text -&gt; {x2 : Int | (x2 == (tLen x1))}</span><span class='hs-varid'>tLength</span></a> <a class=annot href="#"><span class=annottext>{x2 : Text | (x2 == txt)}</span><span class='hs-varid'>txt</span></a> 
<span class=hs-linenum>450: </span>         <span class='hs-keyword'>then</span> <a class=annot href="#"><span class=annottext>x1:Text -&gt; {x5 : Int | (x5 &gt;= 0) &amp;&amp; (x5 &lt; (tLen x1))} -&gt; (IO ())</span><span class='hs-varid'>showCharAt</span></a> <a class=annot href="#"><span class=annottext>{x2 : Text | (x2 == txt)}</span><span class='hs-varid'>txt</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == i)}</span><span class='hs-varid'>i</span></a> 
<span class=hs-linenum>451: </span>         <span class='hs-keyword'>else</span> <a class=annot href="#"><span class=annottext>[Char] -&gt; (IO ())</span><span class='hs-varid'>putStrLn</span></a> <a class=annot href="#"><span class=annottext>{x2 : [Char] | ((len x2) &gt;= 0)}</span><span class='hs-str'>"Bad Input!"</span></a>
</pre>

but this function, which has insufficient sanitization, is **rejected**


<pre><span class=hs-linenum>457: </span><span class='hs-definition'>badMain</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>IO</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>458: </span><a class=annot href="#"><span class=annottext>(IO ())</span><span class='hs-definition'>badMain</span></a> 
<span class=hs-linenum>459: </span>  <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>do</span> <a class=annot href="#"><span class=annottext>Text</span><span class='hs-varid'>txt</span></a> <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>x1:[Char] -&gt; {x2 : Text | ((tLen x2) == (len x1))}</span><span class='hs-varid'>pack</span></a> <a class=annot href="#"><span class=annottext>([Char] -&gt; Text) -&gt; (IO [Char]) -&gt; (IO Text)</span><span class='hs-varop'>&lt;$&gt;</span></a> <a class=annot href="#"><span class=annottext>{x2 : (IO [Char]) | (x2 == System.IO.getLine)}</span><span class='hs-varid'>getLine</span></a> 
<span class=hs-linenum>460: </span>       <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i</span></a>   <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>(IO Int)</span><span class='hs-varid'>readLn</span></a>
<span class=hs-linenum>461: </span>       <span class='hs-keyword'>if</span> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {x2 : Bool | (((Prop x2)) &lt;=&gt; (x1 &lt;= x2))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == i)}</span><span class='hs-varid'>i</span></a> 
<span class=hs-linenum>462: </span>         <span class='hs-keyword'>then</span> <a class=annot href="#"><span class=annottext>x1:Text -&gt; {x5 : Int | (x5 &gt;= 0) &amp;&amp; (x5 &lt; (tLen x1))} -&gt; (IO ())</span><span class='hs-varid'>showCharAt</span></a> <a class=annot href="#"><span class=annottext>{x2 : Text | (x2 == txt)}</span><span class='hs-varid'>txt</span></a> <span class=hs-error><a class=annot href="#"><span class=annottext>{x2 : Int | (x2 == i)}</span><span class='hs-varid'>i</span></a></span> 
<span class=hs-linenum>463: </span>         <span class='hs-keyword'>else</span> <a class=annot href="#"><span class=annottext>[Char] -&gt; (IO ())</span><span class='hs-varid'>putStrLn</span></a> <a class=annot href="#"><span class=annottext>{x2 : [Char] | ((len x2) &gt;= 0)}</span><span class='hs-str'>"Bad Input!"</span></a>
</pre>

Thus, we can use LiquidHaskell to block, at compile time, any serious bleeding
from pointers gone wild.
