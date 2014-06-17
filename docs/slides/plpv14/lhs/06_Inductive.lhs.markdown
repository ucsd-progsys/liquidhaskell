Abstract Refinements {#induction}
=================================

Induction
---------

Encoding *induction* with Abstract refinements

<div class="hidden">


<pre><span class=hs-linenum>12: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Loop</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>13: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varop'>!!</span><span class='hs-layout'>)</span><span class='hs-layout'>,</span> <span class='hs-varid'>foldr</span><span class='hs-layout'>,</span> <span class='hs-varid'>length</span><span class='hs-layout'>,</span> <span class='hs-layout'>(</span><span class='hs-varop'>++</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>14: </span><span class='hs-comment'>-- import Measures</span>
<span class=hs-linenum>15: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span>
<span class=hs-linenum>16: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-termination"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>17: </span>
<span class=hs-linenum>18: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>llen</span>  <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>19: </span>    <span class='hs-varid'>llen</span> <span class='hs-layout'>(</span><span class='hs-conid'>N</span><span class='hs-layout'>)</span>      <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span>
<span class=hs-linenum>20: </span>    <span class='hs-varid'>llen</span> <span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>21: </span>
<span class=hs-linenum>22: </span><span class='hs-definition'>size</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>23: </span><span class='hs-definition'>add</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>24: </span><span class='hs-definition'>loop</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span>
<span class=hs-linenum>25: </span><span class='hs-definition'>foldr</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span>
</pre>
</div>

Induction
=========

Example: `loop` redux 
---------------------

Recall the *higher-order* `loop` 

<br>


<pre><span class=hs-linenum>40: </span><a class=annot href="#"><span class=annottext>forall a &lt;p :: (GHC.Types.Int)-&gt; a-&gt; Bool&gt;.
lo:(Int)
-&gt; hi:{VV : (Int) | (lo &lt;= VV)}
-&gt; {VV : a&lt;p lo&gt; | true}
-&gt; (i:(Int)
    -&gt; {VV : a&lt;p i&gt; | true}
    -&gt; forall [ex:{VV : (Int) | (VV == (i + 1))}].{VV : a&lt;p ex&gt; | true})
-&gt; {VV : a&lt;p hi&gt; | true}</span><span class='hs-definition'>loop</span></a> <a class=annot href="#"><span class=annottext>(Int)</span><span class='hs-varid'>lo</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (lo &lt;= VV)}</span><span class='hs-varid'>hi</span></a> <a class=annot href="#"><span class=annottext>{VV : a | ((papp2 p VV lo))}</span><span class='hs-varid'>base</span></a> <a class=annot href="#"><span class=annottext>i:(Int)
-&gt; {VV : a | ((papp2 p VV i))}
-&gt; forall [ex:{VV : (Int) | (VV == (i + 1))}].{VV : a | ((papp2 p VV ex))}</span><span class='hs-varid'>f</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x4 : (Int) | (x4 &gt;= lo) &amp;&amp; (lo &lt;= x4) &amp;&amp; (x4 &lt;= hi)}
-&gt; {VV : a | ((papp2 p VV x1))} -&gt; {VV : a | ((papp2 p VV hi))}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == lo)}</span><span class='hs-varid'>lo</span></a> <a class=annot href="#"><span class=annottext>{VV : a | ((papp2 p VV lo)) &amp;&amp; (VV == base)}</span><span class='hs-varid'>base</span></a>
<span class=hs-linenum>41: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>42: </span>    <a class=annot href="#"><span class=annottext>i:{VV : (Int) | (VV &gt;= lo) &amp;&amp; (VV &lt;= hi) &amp;&amp; (lo &lt;= VV)}
-&gt; {VV : a | ((papp2 p VV i))} -&gt; {VV : a | ((papp2 p VV hi))}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= lo) &amp;&amp; (VV &lt;= hi) &amp;&amp; (lo &lt;= VV)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>{VV : a | ((papp2 p VV i))}</span><span class='hs-varid'>acc</span></a> 
<span class=hs-linenum>43: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == i) &amp;&amp; (x5 &gt;= lo) &amp;&amp; (lo &lt;= x5) &amp;&amp; (x5 &lt;= hi)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:{x14 : (Int) | (x14 &gt;= i) &amp;&amp; (x14 &gt;= lo) &amp;&amp; (i &lt;= x14) &amp;&amp; (lo &lt;= x14) &amp;&amp; (x14 &lt;= hi)}
-&gt; x2:{x14 : (Int) | (x14 &gt;= i) &amp;&amp; (x14 &gt;= lo) &amp;&amp; (i &lt;= x14) &amp;&amp; (lo &lt;= x14) &amp;&amp; (x14 &lt;= hi)}
-&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == hi) &amp;&amp; (lo &lt;= x3)}</span><span class='hs-varid'>hi</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>i:{VV : (Int) | (VV &gt;= lo) &amp;&amp; (VV &lt;= hi) &amp;&amp; (lo &lt;= VV)}
-&gt; {VV : a | ((papp2 p VV i))} -&gt; {VV : a | ((papp2 p VV hi))}</span><span class='hs-varid'>go</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == i) &amp;&amp; (x5 &gt;= lo) &amp;&amp; (lo &lt;= x5) &amp;&amp; (x5 &lt;= hi)}</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:(Int)
-&gt; {VV : a | ((papp2 p VV x1))}
-&gt; forall [ex:{VV : (Int) | (VV == (x1 + 1))}].{VV : a | ((papp2 p VV ex))}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == i) &amp;&amp; (x5 &gt;= lo) &amp;&amp; (lo &lt;= x5) &amp;&amp; (x5 &lt;= hi)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>{VV : a | ((papp2 p VV i)) &amp;&amp; (VV == acc)}</span><span class='hs-varid'>acc</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>44: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | ((papp2 p VV i)) &amp;&amp; (VV == acc)}</span><span class='hs-varid'>acc</span></a>
</pre>

Iteration Dependence
--------------------

We used `loop` to write 

 <br>
<pre><span class=hs-linenum>53: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>add</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>m</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span><span class='hs-keyword'>|v=m+n}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>54: </span><span class='hs-definition'>add</span> <span class='hs-varid'>n</span> <span class='hs-varid'>m</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>loop</span> <span class='hs-num'>0</span> <span class='hs-varid'>m</span> <span class='hs-varid'>n</span> <span class='hs-layout'>(</span><span class='hs-keyglyph'>\</span><span class='hs-keyword'>_</span> <span class='hs-varid'>i</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>i</span> <span class='hs-varop'>+</span> <span class='hs-num'>1</span><span class='hs-layout'>)</span>
</pre>

<br>

<div class="fragment">

**Problem**

- As property only holds after *last* loop iteration...

- ... cannot instantiate `α` with `{v:Int | v = n + m}`

</div>

Iteration Dependence
--------------------

We used `loop` to write 

 <br>
<pre><span class=hs-linenum>75: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>add</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>m</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span><span class='hs-keyword'>|v=m+n}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>76: </span><span class='hs-definition'>add</span> <span class='hs-varid'>n</span> <span class='hs-varid'>m</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>loop</span> <span class='hs-num'>0</span> <span class='hs-varid'>m</span> <span class='hs-varid'>n</span> <span class='hs-layout'>(</span><span class='hs-keyglyph'>\</span><span class='hs-keyword'>_</span> <span class='hs-varid'>i</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>i</span> <span class='hs-varop'>+</span> <span class='hs-num'>1</span><span class='hs-layout'>)</span>
</pre>

<br>

**Problem** 

Need invariant relating *iteration* `i` with *accumulator* `acc`


Iteration Dependence
--------------------

We used `loop` to write 

 <br>
<pre><span class=hs-linenum>92: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>add</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>m</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span><span class='hs-keyword'>|v=m+n}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>93: </span><span class='hs-definition'>add</span> <span class='hs-varid'>n</span> <span class='hs-varid'>m</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>loop</span> <span class='hs-num'>0</span> <span class='hs-varid'>m</span> <span class='hs-varid'>n</span> <span class='hs-layout'>(</span><span class='hs-keyglyph'>\</span><span class='hs-keyword'>_</span> <span class='hs-varid'>i</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>i</span> <span class='hs-varop'>+</span> <span class='hs-num'>1</span><span class='hs-layout'>)</span>
</pre>

<br>

**Solution** 

- Abstract Refinement `p :: Int -> a -> Prop`

- `(p i acc)` relates *iteration* `i` with *accumulator* `acc`



Induction in `loop` (by hand)
-----------------------------

 <br> 
<pre><span class=hs-linenum>110: </span><span class='hs-definition'>loop</span> <span class='hs-varid'>lo</span> <span class='hs-varid'>hi</span> <span class='hs-varid'>base</span> <span class='hs-varid'>f</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>go</span> <span class='hs-varid'>lo</span> <span class='hs-varid'>base</span>
<span class=hs-linenum>111: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>112: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>i</span> <span class='hs-varid'>acc</span> 
<span class=hs-linenum>113: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>i</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>hi</span>    <span class='hs-keyglyph'>=</span> <span class='hs-varid'>go</span> <span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-varop'>+</span><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>f</span> <span class='hs-varid'>i</span> <span class='hs-varid'>acc</span><span class='hs-layout'>)</span>
<span class=hs-linenum>114: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>acc</span>
</pre>

<br>

<div class="fragment">
<div align="center">

------------  ---   ----------------------------
  **Assume**   :    `out = loop lo hi base f` 

   **Prove**   :    `(p hi out)`
------------  ---   ----------------------------

</div>
</div>


Induction in `loop` (by hand)
-----------------------------

 <br> 
<pre><span class=hs-linenum>136: </span><span class='hs-definition'>loop</span> <span class='hs-varid'>lo</span> <span class='hs-varid'>hi</span> <span class='hs-varid'>base</span> <span class='hs-varid'>f</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>go</span> <span class='hs-varid'>lo</span> <span class='hs-varid'>base</span>
<span class=hs-linenum>137: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>138: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>i</span> <span class='hs-varid'>acc</span> 
<span class=hs-linenum>139: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>i</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>hi</span>    <span class='hs-keyglyph'>=</span> <span class='hs-varid'>go</span> <span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-varop'>+</span><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>f</span> <span class='hs-varid'>i</span> <span class='hs-varid'>acc</span><span class='hs-layout'>)</span>
<span class=hs-linenum>140: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>acc</span>
</pre>

<br>

**Base Case** Initial accumulator `base` satisfies invariant


`(p base lo)`   


Induction in `loop` (by hand)
-----------------------------

 <br> 
<pre><span class=hs-linenum>155: </span><span class='hs-definition'>loop</span> <span class='hs-varid'>lo</span> <span class='hs-varid'>hi</span> <span class='hs-varid'>base</span> <span class='hs-varid'>f</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>go</span> <span class='hs-varid'>lo</span> <span class='hs-varid'>base</span>
<span class=hs-linenum>156: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>157: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>i</span> <span class='hs-varid'>acc</span> 
<span class=hs-linenum>158: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>i</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>hi</span>    <span class='hs-keyglyph'>=</span> <span class='hs-varid'>go</span> <span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-varop'>+</span><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>f</span> <span class='hs-varid'>i</span> <span class='hs-varid'>acc</span><span class='hs-layout'>)</span>
<span class=hs-linenum>159: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>acc</span>
</pre>

<br>

**Inductive Step** `f` *preserves* invariant at `i`


`(p acc i) => (p (f i acc) (i + 1))`

Induction in `loop` (by hand)
-----------------------------

 <br> 
<pre><span class=hs-linenum>173: </span><span class='hs-definition'>loop</span> <span class='hs-varid'>lo</span> <span class='hs-varid'>hi</span> <span class='hs-varid'>base</span> <span class='hs-varid'>f</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>go</span> <span class='hs-varid'>lo</span> <span class='hs-varid'>base</span>
<span class=hs-linenum>174: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>175: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>i</span> <span class='hs-varid'>acc</span> 
<span class=hs-linenum>176: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>i</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>hi</span>    <span class='hs-keyglyph'>=</span> <span class='hs-varid'>go</span> <span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-varop'>+</span><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>f</span> <span class='hs-varid'>i</span> <span class='hs-varid'>acc</span><span class='hs-layout'>)</span>
<span class=hs-linenum>177: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>acc</span>
</pre>

<br>

**"By Induction"** `out` satisfies invariant at `hi` 

`(p out hi)`


Induction in `loop` (by type)
-----------------------------

Induction is an **abstract refinement type** for `loop` 

<br>


<pre><span class=hs-linenum>195: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>loop</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span>
<span class=hs-linenum>196: </span>        <span class='hs-varid'>lo</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> 
<span class=hs-linenum>197: </span>     <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>hi</span><span class='hs-conop'>:</span><span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span><span class='hs-keyword'>|lo &lt;= v}</span>
<span class=hs-linenum>198: </span>     <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>base</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>lo</span><span class='hs-varop'>&gt;</span>                      
<span class=hs-linenum>199: </span>     <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>f</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>i</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-varop'>+</span><span class='hs-num'>1</span><span class='hs-layout'>)</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>200: </span>     <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>hi</span><span class='hs-varop'>&gt;</span>                           <span class='hs-keyword'>@-}</span>
</pre>

<br>

Induction in `loop` (by type)
-----------------------------

`p` is the *index dependent* invariant!


<br> 
<pre><span class=hs-linenum>212: </span><span class='hs-definition'>p</span>    <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span>             <span class='hs-comment'>-- invt </span>
<span class=hs-linenum>213: </span><span class='hs-definition'>base</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>lo</span><span class='hs-varop'>&gt;</span>                      <span class='hs-comment'>-- base </span>
<span class=hs-linenum>214: </span><span class='hs-definition'>f</span>    <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>i</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-varop'>+</span><span class='hs-num'>1</span><span class='hs-layout'>)</span><span class='hs-varop'>&gt;</span> <span class='hs-comment'>-- step</span>
<span class=hs-linenum>215: </span><span class='hs-definition'>out</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>hi</span><span class='hs-varop'>&gt;</span>                      <span class='hs-comment'>-- goal</span>
</pre>



Using Induction
---------------


<pre><span class=hs-linenum>224: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>add</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>m</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span><span class='hs-keyword'>| v=m+n}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>225: </span><a class=annot href="#"><span class=annottext>n:{VV : (Int) | (VV &gt;= 0)}
-&gt; m:{VV : (Int) | (VV &gt;= 0)}
-&gt; {VV : (Int) | (VV == (m + n)) &amp;&amp; (VV &gt;= 0)}</span><span class='hs-definition'>add</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0)}</span><span class='hs-varid'>m</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool&gt;.
x1:(Int)
-&gt; x2:{x21 : (Int) | (x1 &lt;= x21)}
-&gt; {x19 : (Int)&lt;p x1&gt; | (x19 &gt;= 0) &amp;&amp; (x19 &gt;= n) &amp;&amp; (n &lt;= x19)}
-&gt; (i:(Int)
    -&gt; {x19 : (Int)&lt;p i&gt; | (x19 &gt;= 0) &amp;&amp; (x19 &gt;= n) &amp;&amp; (n &lt;= x19)}
    -&gt; forall [ex:{VV : (Int) | (VV == (i + 1))}].{x19 : (Int)&lt;p ex&gt; | (x19 &gt;= 0) &amp;&amp; (x19 &gt;= n) &amp;&amp; (n &lt;= x19)})
-&gt; {x19 : (Int)&lt;p x2&gt; | (x19 &gt;= 0) &amp;&amp; (x19 &gt;= n) &amp;&amp; (n &lt;= x19)}</span><span class='hs-varid'>loop</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == m) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>m</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == n) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>n</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:(Int)
-&gt; x2:{x17 : (Int) | (x17 == (x1 + n)) &amp;&amp; (x17 == (n + x1)) &amp;&amp; (x17 &gt;= 0) &amp;&amp; (x17 &gt;= x1) &amp;&amp; (x17 &gt;= n) &amp;&amp; (x1 &lt;= x17) &amp;&amp; (n &lt;= x17)}
-&gt; {x9 : (Int) | (x9 == (x2 + 1)) &amp;&amp; (x9 &gt; 0) &amp;&amp; (x9 &gt; x1) &amp;&amp; (x9 &gt; x2) &amp;&amp; (x9 &gt; n) &amp;&amp; (x9 &gt;= 0) &amp;&amp; (x1 &lt;= x9) &amp;&amp; (n &lt;= x9)}</span><span class='hs-keyglyph'>\</span></a><span class='hs-keyword'>_</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &gt;= n) &amp;&amp; (n &lt;= VV)}</span><span class='hs-varid'>z</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == z) &amp;&amp; (x5 &gt;= 0) &amp;&amp; (x5 &gt;= n) &amp;&amp; (n &lt;= x5)}</span><span class='hs-varid'>z</span></a> <a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span>
</pre>

<br>

**Verified** by instantiating the abstract refinement of `loop`

`p := \i acc -> acc = i + n`


Using Induction
---------------

 <div/>
<pre><span class=hs-linenum>239: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>add</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>m</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span><span class='hs-keyword'>| v=m+n}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>240: </span><span class='hs-definition'>add</span> <span class='hs-varid'>n</span> <span class='hs-varid'>m</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>loop</span> <span class='hs-num'>0</span> <span class='hs-varid'>m</span> <span class='hs-varid'>n</span> <span class='hs-layout'>(</span><span class='hs-keyglyph'>\</span><span class='hs-keyword'>_</span> <span class='hs-varid'>z</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>z</span> <span class='hs-varop'>+</span> <span class='hs-num'>1</span><span class='hs-layout'>)</span>
</pre>

<br>

Verified by instantiating `p := \i acc -> acc = i + n`

- <div class="fragment">**Base:**  `n = 0 + n`</div>

- <div class="fragment">**Step:**  `acc = i + n  =>  acc + 1 = (i + 1) + n`</div>

- <div class="fragment">**Goal:**  `out = m + n`</div>


Generalizes To Structures 
-------------------------

Same idea applies for induction over *structures* ...


Structural Induction
====================

Example: Lists
--------------

<br>


<pre><span class=hs-linenum>269: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span> 
<span class=hs-linenum>270: </span>         <span class='hs-keyglyph'>|</span> <span class='hs-conid'>C</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
</pre>

<br>

<div class="fragment">
Lets write a generic loop over such lists ...
</div>

Example: `foldr`
----------------

 <br>
<pre><span class=hs-linenum>283: </span><span class='hs-definition'>foldr</span> <span class='hs-varid'>f</span> <span class='hs-varid'>b</span> <span class='hs-conid'>N</span>        <span class='hs-keyglyph'>=</span> <span class='hs-varid'>b</span>
<span class=hs-linenum>284: </span><span class='hs-definition'>foldr</span> <span class='hs-varid'>f</span> <span class='hs-varid'>b</span> <span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>f</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>x</span> <span class='hs-layout'>(</span><span class='hs-varid'>foldr</span> <span class='hs-varid'>f</span> <span class='hs-varid'>b</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>
</pre>

<br>

<div class="fragment">
Lets brace ourselves for the type...
</div>

Example: `foldr`
----------------


<pre><span class=hs-linenum>297: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>foldr</span> <span class='hs-keyglyph'>::</span> 
<span class=hs-linenum>298: </span>    <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span> <span class='hs-varid'>b</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> 
<span class=hs-linenum>299: </span>      <span class='hs-layout'>(</span><span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>xs</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>300: </span>    <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-conid'>N</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>301: </span>    <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>302: </span>    <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>ys</span><span class='hs-varop'>&gt;</span>                            <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>303: </span><a class=annot href="#"><span class=annottext>forall a b &lt;p :: (Loop.L a)-&gt; b-&gt; Bool&gt;.
(xs:(L a)
 -&gt; x:a
 -&gt; {VV : b&lt;p xs&gt; | true}
 -&gt; forall [ex:{VV : (L a) | (VV == (Loop.C x xs))}].{VV : b&lt;p ex&gt; | true})
-&gt; forall [ex:{VV : (L a) | (VV == (Loop.N))}].{VV : b&lt;p ex&gt; | true}
-&gt; ys:(L a)
-&gt; {VV : b&lt;p ys&gt; | true}</span><span class='hs-definition'>foldr</span></a> <a class=annot href="#"><span class=annottext>xs:(L a)
-&gt; x:a
-&gt; {VV : b | ((papp2 p VV xs))}
-&gt; forall [ex:{VV : (L a) | (VV == (Loop.C x xs))}].{VV : b | ((papp2 p VV ex))}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>forall [ex:{VV : (L a) | (VV == (Loop.N))}].{VV : a | ((papp2 p VV ex))}</span><span class='hs-varid'>b</span></a> <span class='hs-conid'>N</span>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall [ex:{VV : (L a) | (VV == (Loop.N))}].{VV : a | ((papp2 p VV ex))}</span><span class='hs-varid'>b</span></a>
<span class=hs-linenum>304: </span><span class='hs-definition'>foldr</span> <span class='hs-varid'>f</span> <span class='hs-varid'>b</span> <span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(L a)
-&gt; x2:a
-&gt; {VV : b | ((papp2 p VV x1))}
-&gt; forall [ex:{VV : (L a) | (VV == (Loop.C x2 x1))}].{VV : b | ((papp2 p VV ex))}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x2 : (L a) | (x2 == xs)}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall &lt;p :: (Loop.L a)-&gt; b-&gt; Bool&gt;.
(xs:(L a)
 -&gt; x:a
 -&gt; {VV : b&lt;p xs&gt; | true}
 -&gt; forall [ex:{VV : (L a) | (VV == (Loop.C x xs))}].{VV : b&lt;p ex&gt; | true})
-&gt; forall [ex:{VV : (L a) | (VV == (Loop.N))}].{VV : b&lt;p ex&gt; | true}
-&gt; x4:(L a)
-&gt; {VV : b&lt;p x4&gt; | true}</span><span class='hs-varid'>foldr</span></a> <a class=annot href="#"><span class=annottext>x1:(L a)
-&gt; x2:a
-&gt; {VV : b | ((papp2 p VV x1))}
-&gt; forall [ex:{VV : (L a) | (VV == (Loop.C x2 x1))}].{VV : b | ((papp2 p VV ex))}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>forall [ex:{VV : (L a) | (VV == (Loop.N))}].{VV : a | ((papp2 p VV ex))}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>{x2 : (L a) | (x2 == xs)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
</pre>

<br>

<div class="fragment">
Lets step through the type...
</div>


`foldr`: Abstract Refinement
----------------------------

 <div/>
<pre><span class=hs-linenum>318: </span><span class='hs-definition'>p</span>    <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span>   
<span class=hs-linenum>319: </span><span class='hs-definition'>step</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>xs</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>320: </span><span class='hs-definition'>base</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-conid'>N</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>321: </span><span class='hs-definition'>ys</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>322: </span><span class='hs-definition'>out</span>  <span class='hs-keyglyph'>::</span>  <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>ys</span><span class='hs-varop'>&gt;</span>                            
</pre>

<br>

`(p xs b)` relates `b` with folded `xs`

`p :: L a -> b -> Prop`


`foldr`: Base Case
------------------

 <div/>
<pre><span class=hs-linenum>336: </span><span class='hs-definition'>p</span>    <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span>   
<span class=hs-linenum>337: </span><span class='hs-definition'>step</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>xs</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>338: </span><span class='hs-definition'>base</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-conid'>N</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>339: </span><span class='hs-definition'>ys</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>340: </span><span class='hs-definition'>out</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>ys</span><span class='hs-varop'>&gt;</span>                            
</pre>

<br>

`base` is related to empty list `N`

`base :: b<p N>` states 



`foldr`: Ind. Step 
------------------

 <div/>
<pre><span class=hs-linenum>355: </span><span class='hs-definition'>p</span>    <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span>   
<span class=hs-linenum>356: </span><span class='hs-definition'>step</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>xs</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>357: </span><span class='hs-definition'>base</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-conid'>N</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>358: </span><span class='hs-definition'>ys</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>359: </span><span class='hs-definition'>out</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>ys</span><span class='hs-varop'>&gt;</span>                            
</pre>

<br>

`step` extends relation from `xs` to `C x xs`

`step :: xs:L a -> x:a -> b<p xs> -> b<p(C x xs)>`


`foldr`: Output
---------------

 <div/>
<pre><span class=hs-linenum>373: </span><span class='hs-definition'>p</span>    <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span>   
<span class=hs-linenum>374: </span><span class='hs-definition'>step</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>xs</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>375: </span><span class='hs-definition'>base</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-conid'>N</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>376: </span><span class='hs-definition'>ys</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>377: </span><span class='hs-definition'>out</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>ys</span><span class='hs-varop'>&gt;</span>                            
</pre>

<br>

Relation holds between `out` and input list `ys`

`out :: b<p ys>`

Using `foldr`: Size
-------------------

We can now verify <br>


<pre><span class=hs-linenum>392: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>size</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span><span class='hs-keyword'>| v = (llen xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>393: </span><a class=annot href="#"><span class=annottext>forall a. xs:(L a) -&gt; {VV : (Int) | (VV == (llen xs))}</span><span class='hs-definition'>size</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (Loop.L a)-&gt; (GHC.Types.Int)-&gt; Bool&gt;.
(xs:(L a)
 -&gt; x:a
 -&gt; {x12 : (Int)&lt;p xs&gt; | (x12 &gt;= 0)}
 -&gt; forall [ex:{VV : (L a) | (VV == (Loop.C x xs))}].{x12 : (Int)&lt;p ex&gt; | (x12 &gt;= 0)})
-&gt; forall [ex:{VV : (L a) | (VV == (Loop.N))}].{x12 : (Int)&lt;p ex&gt; | (x12 &gt;= 0)}
-&gt; x4:(L a)
-&gt; {x12 : (Int)&lt;p x4&gt; | (x12 &gt;= 0)}</span><span class='hs-varid'>foldr</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:(L a)
-&gt; a
-&gt; x3:{x8 : (Int) | (x8 == (llen x1)) &amp;&amp; (x8 &gt;= 0)}
-&gt; {x5 : (Int) | (x5 == (x3 + 1)) &amp;&amp; (x5 &gt; 0) &amp;&amp; (x5 &gt; x3) &amp;&amp; (x5 &gt;= 0)}</span><span class='hs-keyglyph'>\</span></a><span class='hs-keyword'>_</span> <span class='hs-keyword'>_</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0)}</span><span class='hs-varid'>n</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == n) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a>
</pre>

<br>

<div class="fragment">
Verified by automatically instantiating 

`p := \xs acc -> acc = (llen xs)`
</div>

Using `foldr`: Append
---------------------


<pre><span class=hs-linenum>408: </span><span class='hs-keyword'>{-@</span> <span class='hs-layout'>(</span><span class='hs-varop'>++</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Cat</span> <span class='hs-varid'>a</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span> 
<span class=hs-linenum>409: </span><a class=annot href="#"><span class=annottext>(L a)</span><span class='hs-definition'>xs</span></a> <a class=annot href="#"><span class=annottext>forall a.
xs:(L a)
-&gt; ys:(L a)
-&gt; {VV : (L a) | ((llen VV) == ((llen xs) + (llen ys)))}</span><span class='hs-varop'>++</span></a> <a class=annot href="#"><span class=annottext>(L a)</span><span class='hs-varid'>ys</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (Loop.L a)-&gt; (Loop.L a)-&gt; Bool&gt;.
(xs:(L a)
 -&gt; x:a
 -&gt; {x8 : (L a)&lt;p xs&gt; | true}
 -&gt; forall [ex:{VV : (L a) | (VV == (Loop.C x xs))}].{x8 : (L a)&lt;p ex&gt; | true})
-&gt; forall [ex:{VV : (L a) | (VV == (Loop.N))}].{x8 : (L a)&lt;p ex&gt; | true}
-&gt; x4:(L a)
-&gt; {x8 : (L a)&lt;p x4&gt; | true}</span><span class='hs-varid'>foldr</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(L a)
-&gt; a -&gt; x3:(L a) -&gt; {x2 : (L a) | ((llen x2) == (1 + (llen x3)))}</span><span class='hs-keyglyph'>\</span></a><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>a -&gt; x2:(L a) -&gt; {x2 : (L a) | ((llen x2) == (1 + (llen x2)))}</span><span class='hs-conid'>C</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x2 : (L a) | (x2 == ys)}</span><span class='hs-varid'>ys</span></a> <a class=annot href="#"><span class=annottext>{x2 : (L a) | (x2 == xs)}</span><span class='hs-varid'>xs</span></a> 
</pre>

<br>

<div class="fragment">

where the alias `Cat` is:

<br>


<pre><span class=hs-linenum>421: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>Cat</span> <span class='hs-varid'>a</span> <span class='hs-conid'>X</span> <span class='hs-conid'>Y</span> <span class='hs-keyglyph'>=</span> 
<span class=hs-linenum>422: </span>    <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-keyglyph'>|</span><span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-conid'>Y</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

</div>

Using `foldr`: Append
---------------------

 <div/>
<pre><span class=hs-linenum>431: </span><span class='hs-keyword'>{-@</span> <span class='hs-layout'>(</span><span class='hs-varop'>++</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Cat</span> <span class='hs-varid'>a</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span> 
<span class=hs-linenum>432: </span><span class='hs-definition'>xs</span> <span class='hs-varop'>++</span> <span class='hs-varid'>ys</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>foldr</span> <span class='hs-layout'>(</span><span class='hs-keyglyph'>\</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>C</span><span class='hs-layout'>)</span> <span class='hs-varid'>ys</span> <span class='hs-varid'>xs</span> 
</pre>

<br>

<div class="fragment">

Verified by automatically instantiating 

`p := \xs acc -> llen acc = llen xs + llen ys`

</div>

Recap
-----

Abstract refinements decouple *invariant* from *traversal*

<br>

+ <div class="fragment">*reusable* specifications for higher-order functions.</div>

+ <div class="fragment">*automatic* checking and instantiation by SMT.</div>

Recap
-----

1. **Refinements:** Types + Predicates
2. **Subtyping:** SMT Implication
3. **Measures:** Strengthened Constructors
4. **Abstract:** Refinements over Type Signatures
    + *Dependencies*
    + <div class="fragment">*Induction*</div>
