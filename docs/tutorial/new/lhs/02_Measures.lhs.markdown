
 {#measures}
============

Measuring Data Types
--------------------

<div class="hidden">


<pre><span class=hs-linenum>11: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Measures</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>12: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varop'>!!</span><span class='hs-layout'>)</span><span class='hs-layout'>,</span> <span class='hs-varid'>length</span><span class='hs-layout'>)</span>
<span class=hs-linenum>13: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span>
</pre>

</div>

Measuring Data Types 
====================

Example: List lengths 
---------------------

<div class="hidden">


<pre><span class=hs-linenum>27: </span><span class='hs-keyword'>infixr</span> <span class='hs-varop'>`C`</span>
</pre>

</div>

<br>


<pre><span class=hs-linenum>35: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>|</span> <span class='hs-conid'>C</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
</pre>

We define a **measure** for the length of a `List` <br>


<pre><span class=hs-linenum>41: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>llen</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>42: </span>    <span class='hs-varid'>llen</span><span class='hs-layout'>(</span><span class='hs-conid'>N</span><span class='hs-layout'>)</span>      <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span>
<span class=hs-linenum>43: </span>    <span class='hs-varid'>llen</span><span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>44: </span>  <span class='hs-keyword'>@-}</span>
</pre>

<br>

 LiquidHaskell then **automatically strengthens** the types of data constructors
<pre><span class=hs-linenum>50: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>where</span> 
<span class=hs-linenum>51: </span>  <span class='hs-conid'>N</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span>
<span class=hs-linenum>52: </span>  <span class='hs-conid'>C</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span><span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>

Measuring A List's length in logic
----------------------------------

Now we can verify

<br>


<pre><span class=hs-linenum>63: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>length</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = (llen xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>64: </span><span class='hs-definition'>length</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>65: </span><a class=annot href="#"><span class=annottext>forall a.
x1:(Measures.L a) -&gt; {VV : (GHC.Types.Int) | (VV == (llen x1))}</span><span class='hs-definition'>length</span></a> <span class='hs-conid'>N</span>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(GHC.Prim.Int#) -&gt; {x2 : (GHC.Types.Int) | (x2 == (x1  :  int))}</span><span class='hs-num'>0</span></a>
<span class=hs-linenum>66: </span><span class='hs-definition'>length</span> <span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-keyword'>_</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a> <a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int) -&gt; {x4 : (GHC.Types.Int) | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a.
x1:(Measures.L a) -&gt; {VV : (GHC.Types.Int) | (VV == (llen x1))}</span><span class='hs-varid'>length</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Measures.L a) | (x2 == xs)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
</pre>

Measuring A List's length in logic
----------------------------------

And we can type `(!!)` as


<br>


<pre><span class=hs-linenum>78: </span><span class='hs-keyword'>{-@</span> <span class='hs-layout'>(</span><span class='hs-varop'>!!</span><span class='hs-layout'>)</span>     <span class='hs-keyglyph'>::</span> <span class='hs-varid'>ls</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| v &lt; (llen ls)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>79: </span><span class='hs-layout'>(</span><span class='hs-varop'>!!</span><span class='hs-layout'>)</span>         <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>80: </span><span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-keyword'>_</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>forall a.
x1:(Measures.L a)
-&gt; {VV : (GHC.Types.Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; (llen x1))} -&gt; a</span><span class='hs-varop'>!!</span></a> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>81: </span><span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-keyword'>_</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-varop'>!!</span> <span class='hs-varid'>n</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(Measures.L {VV : a | (x &lt;= VV)})</span><span class='hs-varid'>xs</span></a><a class=annot href="#"><span class=annottext>forall a.
x1:(Measures.L a)
-&gt; {VV : (GHC.Types.Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; (llen x1))} -&gt; a</span><span class='hs-varop'>!!</span></a><span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 &gt;= 0)}</span><span class='hs-varid'>n</span></a><a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int) -&gt; {x4 : (GHC.Types.Int) | (x4 == (x1 - x2))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>82: </span><span class='hs-keyword'>_</span>       <span class='hs-varop'>!!</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x1 : [(GHC.Types.Char)] | false} -&gt; {VV : a | false}</span><span class='hs-varid'>liquidError</span></a> <a class=annot href="#"><span class=annottext>{x3 : [(GHC.Types.Char)] | ((len x3) &gt;= 0) &amp;&amp; ((sumLens x3) &gt;= 0)}</span><span class='hs-str'>"This should not happen!"</span></a>
</pre>

<br>

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellMeasure.hs" target= "_blank">Demo:</a> 
Lets see what happens if we **change** the precondition


Another measure for List
--------------------------

We define a new **measure** to check nullity of a `List` <br>


<pre><span class=hs-linenum>97: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>isNull</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span>
<span class=hs-linenum>98: </span>    <span class='hs-varid'>isNull</span><span class='hs-layout'>(</span><span class='hs-conid'>N</span><span class='hs-layout'>)</span>      <span class='hs-keyglyph'>=</span> <span class='hs-varid'>true</span>
<span class=hs-linenum>99: </span>    <span class='hs-varid'>isNull</span><span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>false</span>
<span class=hs-linenum>100: </span>  <span class='hs-keyword'>@-}</span>
</pre>

<br>

 LiquidHaskell then **automatically strengthens** the types of data constructors
<pre><span class=hs-linenum>106: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>where</span> 
<span class=hs-linenum>107: </span>  <span class='hs-conid'>N</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>isNull</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span>
<span class=hs-linenum>108: </span>  <span class='hs-conid'>C</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>not</span> <span class='hs-layout'>(</span><span class='hs-varid'>isNull</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>



Multiple measures for List
--------------------------

The types of data constructors will be the **conjuction** of all the inferred types:


 The types from `llen` definition
<pre><span class=hs-linenum>120: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>where</span> 
<span class=hs-linenum>121: </span>  <span class='hs-conid'>N</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span>
<span class=hs-linenum>122: </span>  <span class='hs-conid'>C</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span><span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>

<br>
 and the types from `isNull`
<pre><span class=hs-linenum>127: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>where</span> 
<span class=hs-linenum>128: </span>  <span class='hs-conid'>N</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>isNull</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span>
<span class=hs-linenum>129: </span>  <span class='hs-conid'>C</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>not</span> <span class='hs-layout'>(</span><span class='hs-varid'>isNull</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>


<br>
 So, the final types will be
<pre><span class=hs-linenum>135: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>where</span> 
<span class=hs-linenum>136: </span>  <span class='hs-conid'>N</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-layout'>(</span><span class='hs-varid'>isNull</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>137: </span>  <span class='hs-conid'>C</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span><span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>not</span> <span class='hs-layout'>(</span><span class='hs-varid'>isNull</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>


Invariants in Data Constructors
------------------------------

We can refine the definition of data types setting **invariants**

<pre><span class=hs-linenum>146: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span>
<span class=hs-linenum>147: </span>             <span class='hs-keyglyph'>|</span> <span class='hs-conid'>C</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>xs</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>x</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span><span class='hs-layout'>)</span>  <span class='hs-keyword'>@-}</span>
</pre>

<br>

 As before,the types of data constuctors are strengthened to
<pre><span class=hs-linenum>153: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>154: </span>  <span class='hs-conid'>N</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>155: </span>  <span class='hs-conid'>C</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span> <span class='hs-conid'>L</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>x</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span>
</pre>

LiquidHaskell

- **Proves** the property when `C` is called

- **Assumes** the property when `C` is opened



Increasing Lists
-----------------

This invariant constrains all Lists to **increasing**

<pre><span class=hs-linenum>171: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span>
<span class=hs-linenum>172: </span>             <span class='hs-keyglyph'>|</span> <span class='hs-conid'>C</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>xs</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>x</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span><span class='hs-layout'>)</span>  <span class='hs-keyword'>@-}</span>
</pre>

<br>
<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellInsertSort.hs"
target= "_blank">Insert sort</a> 

<pre><span class=hs-linenum>179: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>insert</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>180: </span><span class='hs-definition'>insert</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>181: </span><a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
a -&gt; (Measures.L a) -&gt; (Measures.L a)</span><span class='hs-definition'>insert</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>y</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-varop'>`C`</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:a
-&gt; x2:a -&gt; {x2 : (GHC.Types.Bool) | (((Prop x2)) &lt;=&gt; (x1 &lt;= x2))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:{VV : a | (VV &gt;= x)}
-&gt; x2:(Measures.L {VV : a | (VV &gt;= x) &amp;&amp; (x1 &lt;= VV)})
-&gt; {x3 : (Measures.L {VV : a | (VV &gt;= x)}) | (((isNull x3)) &lt;=&gt; false) &amp;&amp; ((llen x3) == (1 + (llen x2)))}</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
a -&gt; (Measures.L a) -&gt; (Measures.L a)</span><span class='hs-varid'>insert</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Measures.L {VV : a | (x &lt;= VV)}) | (x2 == xs)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>182: </span>                    <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>x1:{VV : a | (VV &gt;= y)}
-&gt; x2:(Measures.L {VV : a | (VV &gt;= y) &amp;&amp; (x1 &lt;= VV)})
-&gt; {x3 : (Measures.L {VV : a | (VV &gt;= y)}) | (((isNull x3)) &lt;=&gt; false) &amp;&amp; ((llen x3) == (1 + (llen x2)))}</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>forall a.
(GHC.Classes.Ord a) =&gt;
a -&gt; (Measures.L a) -&gt; (Measures.L a)</span><span class='hs-varid'>insert</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Measures.L {VV : a | (x &lt;= VV)}) | (x2 == xs)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>183: </span>
<span class=hs-linenum>184: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>insertSort</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>185: </span><span class='hs-definition'>insertSort</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>186: </span><a class=annot href="#"><span class=annottext>forall a. (GHC.Classes.Ord a) =&gt; [a] -&gt; (Measures.L a)</span><span class='hs-definition'>insertSort</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(a -&gt; (Measures.L a) -&gt; (Measures.L a))
-&gt; (Measures.L a) -&gt; [a] -&gt; (Measures.L a)</span><span class='hs-varid'>foldr</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (Measures.L a) -&gt; (Measures.L a)</span><span class='hs-varid'>insert</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Measures.L {VV : a | false}) | (((isNull x3)) &lt;=&gt; true) &amp;&amp; ((llen x3) == 0)}</span><span class='hs-conid'>N</span></a>
</pre>

<br>
What if increasing and decreasing lists should co-exist?

We use **abstract refinements** to allow it!


Recap: Refinement Types
-----------------------

1. **Refinements:** Types + Predicates
2. **Subtyping:** SMT Implication
3. <div class="fragment">**Measures:** Strengthened Constructors</div>

