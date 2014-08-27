Termination {#termination}
==========================


<div class="hidden">

<pre><span class=hs-linenum> 7: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Termination</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum> 8: </span>
<span class=hs-linenum> 9: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>gcd</span><span class='hs-layout'>,</span> <span class='hs-varid'>mod</span><span class='hs-layout'>,</span> <span class='hs-varid'>map</span><span class='hs-layout'>)</span>
<span class=hs-linenum>10: </span><span class='hs-definition'>fib</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>11: </span><span class='hs-definition'>gcd</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>12: </span><span class='hs-keyword'>infixr</span> <span class='hs-varop'>`C`</span>
<span class=hs-linenum>13: </span>
<span class=hs-linenum>14: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>|</span> <span class='hs-conid'>C</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>15: </span>
<span class=hs-linenum>16: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>invariant</span> <span class='hs-keyword'>{v:</span> <span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyword'>| 0 &lt;= (llen v)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>17: </span>
<span class=hs-linenum>18: </span><span class='hs-definition'>mod</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>19: </span><a class=annot href="#"><span class=annottext>x1:{VV : (Int) | (VV &gt;= 0)}
-&gt; x2:{VV : (Int) | (VV &gt;= 0) &amp;&amp; (0 &lt; VV) &amp;&amp; (VV &lt; x1)}
-&gt; {VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; x2)}</span><span class='hs-definition'>mod</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0) &amp;&amp; (0 &lt; VV) &amp;&amp; (VV &lt; a)}</span><span class='hs-varid'>b</span></a> <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == a) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 - x2))}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == b) &amp;&amp; (x5 &gt;= 0) &amp;&amp; (0 &lt; x5) &amp;&amp; (x5 &lt; a)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>x1:{x10 : (Int) | (x10 &gt; 0) &amp;&amp; (0 &lt; x10) &amp;&amp; (x10 &lt; a)}
-&gt; x2:{x10 : (Int) | (x10 &gt; 0) &amp;&amp; (0 &lt; x10) &amp;&amp; (x10 &lt; a)}
-&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 &gt; x2))}</span><span class='hs-varop'>&gt;</span></a>  <a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == b) &amp;&amp; (x5 &gt;= 0) &amp;&amp; (0 &lt; x5) &amp;&amp; (x5 &lt; a)}</span><span class='hs-varid'>b</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{VV : (Int) | (VV &gt;= 0)}
-&gt; x2:{VV : (Int) | (VV &gt;= 0) &amp;&amp; (0 &lt; VV) &amp;&amp; (VV &lt; x1)}
-&gt; {VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; x2)}</span><span class='hs-varid'>mod</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == a) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 - x2))}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == b) &amp;&amp; (x5 &gt;= 0) &amp;&amp; (0 &lt; x5) &amp;&amp; (x5 &lt; a)}</span><span class='hs-varid'>b</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == b) &amp;&amp; (x5 &gt;= 0) &amp;&amp; (0 &lt; x5) &amp;&amp; (x5 &lt; a)}</span><span class='hs-varid'>b</span></a>
<span class=hs-linenum>20: </span>        <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == a) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 - x2))}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == b) &amp;&amp; (x5 &gt;= 0) &amp;&amp; (0 &lt; x5) &amp;&amp; (x5 &lt; a)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>x1:{x12 : (Int) | (x12 &gt; 0) &amp;&amp; (0 &lt; x12) &amp;&amp; (x12 &lt; a) &amp;&amp; (x12 &lt;= b)}
-&gt; x2:{x12 : (Int) | (x12 &gt; 0) &amp;&amp; (0 &lt; x12) &amp;&amp; (x12 &lt; a) &amp;&amp; (x12 &lt;= b)}
-&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>&lt;</span></a>  <a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == b) &amp;&amp; (x5 &gt;= 0) &amp;&amp; (0 &lt; x5) &amp;&amp; (x5 &lt; a)}</span><span class='hs-varid'>b</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == a) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 - x2))}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == b) &amp;&amp; (x5 &gt;= 0) &amp;&amp; (0 &lt; x5) &amp;&amp; (x5 &lt; a)}</span><span class='hs-varid'>b</span></a>
<span class=hs-linenum>21: </span>        <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == a) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 - x2))}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == b) &amp;&amp; (x5 &gt;= 0) &amp;&amp; (0 &lt; x5) &amp;&amp; (x5 &lt; a)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>x1:{x12 : (Int) | (x12 == b) &amp;&amp; (x12 &gt; 0) &amp;&amp; (0 &lt; x12) &amp;&amp; (x12 &lt; a)}
-&gt; x2:{x12 : (Int) | (x12 == b) &amp;&amp; (x12 &gt; 0) &amp;&amp; (0 &lt; x12) &amp;&amp; (x12 &lt; a)}
-&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 == x2))}</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == b) &amp;&amp; (x5 &gt;= 0) &amp;&amp; (0 &lt; x5) &amp;&amp; (x5 &lt; a)}</span><span class='hs-varid'>b</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(Int#) -&gt; {x2 : (Int) | (x2 == (x1  :  int))}</span><span class='hs-num'>0</span></a>
<span class=hs-linenum>22: </span>
<span class=hs-linenum>23: </span><span class='hs-definition'>merge</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span>
</pre>
</div>

Dependent != Refinement
-----------------------

<div class="fragment">**Dependent Types**</div>

+ <div class="fragment">*Arbitrary terms* appear inside types</div> 
+ <div class="fragment">Termination ensures well-defined</div>

<br>

<div class="fragment">**Refinement Types**</div>

+ <div class="fragment">*Restricted refinements* appear in types</div>
+ <div class="fragment">Termination *not* required ...</div> 
+ <div class="fragment">... except, alas, with *lazy* evaluation!</div>

Refinements & Termination
----------------------------

<div class="fragment">
Fortunately, we can ensure termination *using refinements*
</div>


Main Idea
---------

Recursive calls must be on *smaller* inputs

<br>

+ [Turing](http://classes.soe.ucsc.edu/cmps210/Winter11/Papers/turing-1936.pdf)
+ [Sized Types](http://dl.acm.org/citation.cfm?id=240882)

Recur On *Smaller* `Nat` 
------------------------

<div class="fragment">

**To ensure termination of**

 <div/>
<pre><span class=hs-linenum>69: </span><span class='hs-definition'>foo</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>T</span>
<span class=hs-linenum>70: </span><span class='hs-definition'>foo</span> <span class='hs-varid'>x</span> <span class='hs-keyglyph'>=</span>  <span class='hs-varid'>body</span>
</pre>

</div>

<br>

<div class="fragment">
**Check `body` Under Assumption**

`foo :: {v:Nat | v < x} -> T`

<br>

*i.e.* require recursive calls have inputs *smaller* than `x`
</div>



Ex: Recur On *Smaller* `Nat` 
----------------------------


<pre><span class=hs-linenum>93: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fib</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Nat</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>94: </span><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0)} -&gt; {VV : (Int) | (VV &gt;= 0)}</span><span class='hs-definition'>fib</span></a> <span class='hs-num'>0</span>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(Int#) -&gt; {x2 : (Int) | (x2 == (x1  :  int))}</span><span class='hs-num'>1</span></a>
<span class=hs-linenum>95: </span><span class='hs-definition'>fib</span> <span class='hs-num'>1</span>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(Int#) -&gt; {x2 : (Int) | (x2 == (x1  :  int))}</span><span class='hs-num'>1</span></a>
<span class=hs-linenum>96: </span><span class='hs-definition'>fib</span> <span class='hs-varid'>n</span>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0)} -&gt; {VV : (Int) | (VV &gt;= 0)}</span><span class='hs-varid'>fib</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 &gt;= 0)}</span><span class='hs-varid'>n</span></a><a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 - x2))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0)} -&gt; {VV : (Int) | (VV &gt;= 0)}</span><span class='hs-varid'>fib</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 &gt;= 0)}</span><span class='hs-varid'>n</span></a><a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 - x2))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (2  :  int))}</span><span class='hs-num'>2</span></a><span class='hs-layout'>)</span>
</pre>

<br>

<div class="fragment">
Terminates, as both `n-1` and `n-2` are `< n`
</div>

<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=GCD.hs" target="_blank">Demo:</a>What if we drop the `fib 1` case?
</div>

Refinements Are Essential!
--------------------------


<pre><span class=hs-linenum>115: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>gcd</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{b:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| b &lt; a}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>116: </span><a class=annot href="#"><span class=annottext>x1:{VV : (Int) | (VV &gt;= 0)}
-&gt; {VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; x1)} -&gt; (Int)</span><span class='hs-definition'>gcd</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0)}</span><span class='hs-varid'>a</span></a> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == a) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>a</span></a>
<span class=hs-linenum>117: </span><span class='hs-definition'>gcd</span> <span class='hs-varid'>a</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{VV : (Int) | (VV &gt;= 0)}
-&gt; {VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; x1)} -&gt; (Int)</span><span class='hs-varid'>gcd</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 &gt;= 0) &amp;&amp; (x3 &lt; a)}</span><span class='hs-varid'>b</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == a) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x1:{x9 : (Int) | (x9 &gt;= 0)}
-&gt; x2:{x7 : (Int) | (x7 &gt;= 0) &amp;&amp; (0 &lt; x7) &amp;&amp; (x7 &lt; x1)}
-&gt; {x3 : (Int) | (x3 &gt;= 0) &amp;&amp; (x3 &lt; x2)}</span><span class='hs-varop'>`mod`</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 &gt;= 0) &amp;&amp; (x3 &lt; a)}</span><span class='hs-varid'>b</span></a><span class='hs-layout'>)</span>
</pre>

<br>

<div class="fragment">
Need refinements to prove `(a mod b) < b` at *recursive* call!
</div>

<br>

<div class="fragment">

<pre><span class=hs-linenum>130: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>mod</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> 
<span class=hs-linenum>131: </span>        <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-conop'>:</span><span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span><span class='hs-keyword'>|(0 &lt; v &amp;&amp; v &lt; a)}</span> 
<span class=hs-linenum>132: </span>        <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span><span class='hs-keyword'>| v &lt; b}</span>                 <span class='hs-keyword'>@-}</span>
</pre>
</div>

Recur On *Smaller* Inputs
-------------------------

What of input types other than `Nat` ?

<div/>
<pre><span class=hs-linenum>142: </span><span class='hs-definition'>foo</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>S</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>T</span>
<span class=hs-linenum>143: </span><span class='hs-definition'>foo</span> <span class='hs-varid'>x</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>body</span>
</pre>

<br>

<div class="fragment">
**Reduce** to `Nat` case...
</div>

<br>

Recur On *Smaller* Inputs
-------------------------

What of input types other than `Nat` ?

<div/>
<pre><span class=hs-linenum>160: </span><span class='hs-definition'>foo</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>S</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>T</span>
<span class=hs-linenum>161: </span><span class='hs-definition'>foo</span> <span class='hs-varid'>x</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>body</span>
</pre>

<br>

Specify a **default measure** `mS :: S -> Int`

<br>

<div class="fragment">
**Check `body` Under Assumption**

`foo :: {v:s | 0 <= (mS v) < (mS x)} -> T`
</div>


Ex: Recur on *smaller* `List`
-----------------------------

 
<pre><span class=hs-linenum>181: </span><a class=annot href="#"><span class=annottext>forall a b. (a -&gt; b) -&gt; (L a) -&gt; (L b)</span><span class='hs-definition'>map</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <span class='hs-conid'>N</span>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a. {x2 : (L a) | ((llen x2) == 0)}</span><span class='hs-conid'>N</span></a>
<span class=hs-linenum>182: </span><span class='hs-definition'>map</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>a -&gt; x2:(L a) -&gt; {x2 : (L a) | ((llen x2) == (1 + (llen x2)))}</span><span class='hs-varop'>`C`</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a b. (a -&gt; b) -&gt; (L a) -&gt; (L b)</span><span class='hs-varid'>map</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x3 : (L a) | (x3 == xs) &amp;&amp; (0 &lt;= (llen x3))}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span> 
</pre>

<br>

Terminates using **default** measure `llen`

<div class="fragment">

<pre><span class=hs-linenum>191: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>llen</span><span class='hs-keyglyph'>]</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span> 
<span class=hs-linenum>192: </span>                    <span class='hs-keyglyph'>|</span> <span class='hs-conid'>C</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-keyglyph'>::</span><span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>xs</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>193: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>llen</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>194: </span>    <span class='hs-varid'>llen</span> <span class='hs-layout'>(</span><span class='hs-conid'>N</span><span class='hs-layout'>)</span>      <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span>
<span class=hs-linenum>195: </span>    <span class='hs-varid'>llen</span> <span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span>   <span class='hs-keyword'>@-}</span>
</pre>
</div>


Recur On *Smaller* Inputs
-------------------------

What of *smallness* spread across inputs?

<br>


<pre><span class=hs-linenum>208: </span><a class=annot href="#"><span class=annottext>forall a. (Ord a) =&gt; (L a) -&gt; (L a) -&gt; (L a)</span><span class='hs-definition'>merge</span></a> <a class=annot href="#"><span class=annottext>(L a)</span><span class='hs-varid'>xs</span></a><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-varop'>`C`</span> <span class='hs-varid'>xs'</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>(L a)</span><span class='hs-varid'>ys</span></a><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-varid'>y</span> <span class='hs-varop'>`C`</span> <span class='hs-varid'>ys'</span><span class='hs-layout'>)</span>
<span class=hs-linenum>209: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; x2:a -&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>a -&gt; x2:(L a) -&gt; {x2 : (L a) | ((llen x2) == (1 + (llen x2)))}</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>forall a. (Ord a) =&gt; (L a) -&gt; (L a) -&gt; (L a)</span><span class='hs-varid'>merge</span></a> <a class=annot href="#"><span class=annottext>{x3 : (L a) | (x3 == xs') &amp;&amp; (0 &lt;= (llen x3))}</span><span class='hs-varid'>xs'</span></a> <a class=annot href="#"><span class=annottext>{x5 : (L a) | (x5 == ys) &amp;&amp; (x5 == (Termination.C y ys')) &amp;&amp; ((llen x5) == (1 + (llen ys'))) &amp;&amp; (0 &lt;= (llen x5))}</span><span class='hs-varid'>ys</span></a>
<span class=hs-linenum>210: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>a -&gt; x2:(L a) -&gt; {x2 : (L a) | ((llen x2) == (1 + (llen x2)))}</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>forall a. (Ord a) =&gt; (L a) -&gt; (L a) -&gt; (L a)</span><span class='hs-varid'>merge</span></a> <a class=annot href="#"><span class=annottext>{x5 : (L a) | (x5 == xs) &amp;&amp; (x5 == (Termination.C x xs')) &amp;&amp; ((llen x5) == (1 + (llen xs'))) &amp;&amp; (0 &lt;= (llen x5))}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>{x3 : (L a) | (x3 == ys') &amp;&amp; (0 &lt;= (llen x3))}</span><span class='hs-varid'>ys'</span></a>
</pre>

<br>

<div class="fragment">
Neither input decreases, but their *sum* does.
</div>

Recur On *Smaller* Inputs
-------------------------

Neither input decreases, but their *sum* does.

<br>


<pre><span class=hs-linenum>227: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>merge</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>_</span> 
<span class=hs-linenum>228: </span>          <span class='hs-varop'>/</span>  <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>llen</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span>     <span class='hs-keyword'>@-}</span>
</pre>

<br>

<div class="fragment">

Synthesize *ghost* parameter equal to `[...]`

</div>

<br>

<div class="fragment">

Reduces to single-parameter-decrease case. 

</div>

Important Extensions 
--------------------

- <div class="fragment">Mutual recursion</div>

- <div class="fragment">Lexicographic ordering...</div>

Recap
-----

Main idea: Recursive calls on *smaller inputs*

<br>

- <div class="fragment">Use refinements to *check* smaller</div>

- <div class="fragment">Use refinements to *establish* smaller</div>


A Curious Circularity
---------------------

<div class="fragment">Refinements require termination ...</div> 

<br>

<div class="fragment">... Termination requires refinements!</div>

<br>

<div class="fragment"> (Meta-theory is tricky, but all ends well.)</div>


Recap
-----

1. **Refinements:** Types + Predicates
2. **Subtyping:** SMT Implication
3. **Measures:** Strengthened Constructors
4. **Abstract Refinements:* Decouple Invariants 
5. **Lazy Evaluation:** Requires Termination
6. **Termination:** Via Refinements!
7. <div class="fragment">**Evaluation** </div>


