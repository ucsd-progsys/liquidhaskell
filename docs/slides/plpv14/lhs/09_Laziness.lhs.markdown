 {#laziness}
============

<div class="hidden">

<pre><span class=hs-linenum>6: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Laziness</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>7: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span>
<span class=hs-linenum>8: </span>
<span class=hs-linenum>9: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-termination"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>10: </span>
<span class=hs-linenum>11: </span><span class='hs-definition'>divide</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>12: </span><span class='hs-definition'>foo</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>13: </span><span class='hs-comment'>-- zero    :: Int </span>
<span class=hs-linenum>14: </span><span class='hs-comment'>-- diverge :: a -&gt; b</span>
</pre>
</div>


Lazy Evaluation?
----------------

Lazy Evaluation
===============

SMT based Verification
----------------------

Techniques developed for *strict* languages

<br>

<div class="fragment">

-----------------------   ---   ------------------------------------------
        **Floyd-Hoare**    :    `ESCJava`, `SpecSharp` ...
     **Model Checkers**    :    `Slam`, `Blast` ...
   **Refinement Types**    :    `DML`, `Stardust`, `F7`, `F*`, `Sage` ...
-----------------------   ---   ------------------------------------------

</div>

<br>

<div class="fragment">
Surely soundness carries over to Haskell, right?
</div>


Back To the Beginning
---------------------


<pre><span class=hs-linenum>53: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>divide</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span><span class='hs-keyword'>| v /= 0}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>54: </span><a class=annot href="#"><span class=annottext>(Int) -&gt; {VV : (Int) | (VV /= 0)} -&gt; (Int)</span><span class='hs-definition'>divide</span></a> <a class=annot href="#"><span class=annottext>(Int)</span><span class='hs-varid'>n</span></a> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : [(Char)] | false} -&gt; {x1 : (Int) | false}</span><span class='hs-varid'>liquidError</span></a> <a class=annot href="#"><span class=annottext>{x3 : [(Char)] | ((len x3) &gt;= 0) &amp;&amp; ((sumLens x3) &gt;= 0)}</span><span class='hs-str'>"div-by-zero!"</span></a>
<span class=hs-linenum>55: </span><span class='hs-definition'>divide</span> <span class='hs-varid'>n</span> <span class='hs-varid'>d</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == n)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:(Int)
-&gt; x2:(Int)
-&gt; {x6 : (Int) | (((x1 &gt;= 0) &amp;&amp; (x2 &gt;= 0)) =&gt; (x6 &gt;= 0)) &amp;&amp; (((x1 &gt;= 0) &amp;&amp; (x2 &gt;= 1)) =&gt; (x6 &lt;= x1)) &amp;&amp; (x6 == (x1 / x2))}</span><span class='hs-varop'>`div`</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 /= 0)}</span><span class='hs-varid'>d</span></a>
</pre>

<br>

<div class="fragment">
Should only try to `divide` by non-zero values
</div>

An Innocent Function
--------------------

`foo` returns a value *strictly less than* input.

<br>


<pre><span class=hs-linenum>72: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>foo</span>       <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span> <span class='hs-keyword'>| v &lt; n}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>73: </span><a class=annot href="#"><span class=annottext>n:{VV : (Int) | (VV &gt;= 0)} -&gt; {VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; n)}</span><span class='hs-definition'>foo</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0)}</span><span class='hs-varid'>n</span></a>   
<span class=hs-linenum>74: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == n) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:{x8 : (Int) | (x8 &gt;= 0) &amp;&amp; (x8 &lt;= n)}
-&gt; x2:{x8 : (Int) | (x8 &gt;= 0) &amp;&amp; (x8 &lt;= n)}
-&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 &gt; x2))}</span><span class='hs-varop'>&gt;</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == n) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 - x2))}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a>
<span class=hs-linenum>75: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x5 : (Int) | (x5 &gt;= 0)}
-&gt; {x3 : (Int) | (x3 &gt;= 0) &amp;&amp; (x3 &lt; x1)}</span><span class='hs-varid'>foo</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == n) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>n</span></a>
</pre>

LiquidHaskell Lies! 
-------------------


<pre><span class=hs-linenum>82: </span><a class=annot href="#"><span class=annottext>(Int)</span><span class='hs-definition'>explode</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>let</span> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (0  :  int))}</span><span class='hs-varid'>z</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a>
<span class=hs-linenum>83: </span>          <span class='hs-keyword'>in</span>  <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x:{VV : (Int) | (VV == 0) &amp;&amp; (VV == 1) &amp;&amp; (VV == Laziness.explode) &amp;&amp; (VV == z) &amp;&amp; (VV &gt; 0) &amp;&amp; (VV &gt; Laziness.explode) &amp;&amp; (VV &gt; z) &amp;&amp; (VV &lt; 0) &amp;&amp; (VV &lt; Laziness.explode) &amp;&amp; (VV &lt; z)}
-&gt; {VV : (Int) | (VV == 0) &amp;&amp; (VV == 1) &amp;&amp; (VV == Laziness.explode) &amp;&amp; (VV == x) &amp;&amp; (VV == z) &amp;&amp; (VV &gt; 0) &amp;&amp; (VV &gt; Laziness.explode) &amp;&amp; (VV &gt; x) &amp;&amp; (VV &gt; z) &amp;&amp; (VV &lt; 0) &amp;&amp; (VV &lt; Laziness.explode) &amp;&amp; (VV &lt; x) &amp;&amp; (VV &lt; z)}</span><span class='hs-keyglyph'>\</span></a><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV == 0) &amp;&amp; (VV == 1) &amp;&amp; (VV == Laziness.explode) &amp;&amp; (VV == z) &amp;&amp; (VV &gt; 0) &amp;&amp; (VV &gt; Laziness.explode) &amp;&amp; (VV &gt; z) &amp;&amp; (VV &lt; 0) &amp;&amp; (VV &lt; Laziness.explode) &amp;&amp; (VV &lt; z)}</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (2013  :  int))}</span><span class='hs-num'>2013</span></a> <a class=annot href="#"><span class=annottext>(Int) -&gt; {x3 : (Int) | (x3 /= 0)} -&gt; (Int)</span><span class='hs-varop'>`divide`</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == z) &amp;&amp; (x3 == (0  :  int))}</span><span class='hs-varid'>z</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:{x5 : (Int) | (x5 &gt;= 0)}
-&gt; {x3 : (Int) | (x3 &gt;= 0) &amp;&amp; (x3 &lt; x1)}</span><span class='hs-varid'>foo</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == z) &amp;&amp; (x3 == (0  :  int))}</span><span class='hs-varid'>z</span></a><span class='hs-layout'>)</span>
</pre>

<br>

<div class="fragment">
Why is this deemed *safe*? 
</div>

<br>

<div class="fragment">
(Where's the *red* highlight when you want it?)
</div>


Safe With Eager Eval
--------------------

 <div/>
<pre><span class=hs-linenum>103: </span><span class='hs-comment'>{- foo       :: n:Nat -&gt; {v:Nat | v &lt; n} -}</span>
<span class=hs-linenum>104: </span><span class='hs-definition'>foo</span> <span class='hs-varid'>n</span>   
<span class=hs-linenum>105: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>n</span> <span class='hs-varop'>&gt;</span> <span class='hs-num'>0</span>     <span class='hs-keyglyph'>=</span> <span class='hs-varid'>n</span> <span class='hs-comment'>-</span> <span class='hs-num'>1</span>
<span class=hs-linenum>106: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>foo</span> <span class='hs-varid'>n</span>
<span class=hs-linenum>107: </span>
<span class=hs-linenum>108: </span><span class='hs-definition'>explode</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>let</span> <span class='hs-varid'>z</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span>
<span class=hs-linenum>109: </span>          <span class='hs-keyword'>in</span>  <span class='hs-layout'>(</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>x</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-num'>2013</span> <span class='hs-varop'>`divide`</span> <span class='hs-varid'>z</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>foo</span> <span class='hs-varid'>z</span><span class='hs-layout'>)</span>
</pre>

<br>

<div class="fragment">
In Java, ML, etc: program spins away, *never hits* divide-by-zero 
</div>

Unsafe With Lazy Eval
---------------------

<div/>
<pre><span class=hs-linenum>122: </span><span class='hs-comment'>{- foo       :: n:Nat -&gt; {v:Nat | v &lt; n} -}</span>
<span class=hs-linenum>123: </span><span class='hs-definition'>foo</span> <span class='hs-varid'>n</span>   
<span class=hs-linenum>124: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>n</span> <span class='hs-varop'>&gt;</span> <span class='hs-num'>0</span>     <span class='hs-keyglyph'>=</span> <span class='hs-varid'>n</span> <span class='hs-comment'>-</span> <span class='hs-num'>1</span>
<span class=hs-linenum>125: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>foo</span> <span class='hs-varid'>n</span>
<span class=hs-linenum>126: </span>
<span class=hs-linenum>127: </span><span class='hs-definition'>explode</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>let</span> <span class='hs-varid'>z</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span>
<span class=hs-linenum>128: </span>          <span class='hs-keyword'>in</span>  <span class='hs-layout'>(</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>x</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-num'>2013</span> <span class='hs-varop'>`divide`</span> <span class='hs-varid'>z</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>foo</span> <span class='hs-varid'>z</span><span class='hs-layout'>)</span>
</pre>

<br>

In Haskell, program *skips* `(foo z)` & hits divide-by-zero!

Problem: Divergence
-------------------

<div class="fragment">
What is denoted by `e :: {v:Int | 0 <= v}` ?
</div>

<br>

<div class="fragment">
`e` evaluates to a `Nat`  
</div>

<div class="fragment">
or

**diverges**! 
</div>

<div class="fragment">
<br>

Classical Floyd-Hoare notion of [partial correctness](http://en.wikipedia.org/wiki/Hoare_logic#Partial_and_total_correctness)

</div>



Problem: Divergence
-------------------

Suppose `e :: {v:Int | 0 <= v}`

<br>

**Consider**

`let x = e in body`

With Eager Evaluation 
---------------------

Suppose `e :: {v:Int | 0 <= v}`

<br>

**Consider**

`let x = e in body`

<br>

<div class="fragment">
**Can** assume `x` is a `Nat` when checking `body`
</div>

But With Lazy Evaluation 
------------------------

Suppose `e :: {v:Int | 0 <= v}`

<br>

**Consider**

`let x = e in body`

<br>

<div class="fragment">
**Cannot** assume `x` is a `Nat` when checking e!
</div>

Oops. Now what?
---------------

**Solution** 

Only assign *non-trivial* refinements to *non-diverging* terms!

<br>

<div class="fragment">

**Require A Termination Analysis**

(Oh dear.)

</div>

<a href="http://goto.ucsd.edu:8090/index.html#?demo=TellingLies.hs" target="_blank">Demo:</a>Disable `"--no-termination" and see what happens!


Recap
-----

1. **Refinements:** Types + Predicates
2. **Subtyping:** SMT Implication
3. **Measures:** Strengthened Constructors
4. **Abstract Refinements:* Decouple Invariants 
5. **Lazy Evaluation:** Requires Termination
6. <div class="fragment">**Termination:** Via Refinements!</div>

