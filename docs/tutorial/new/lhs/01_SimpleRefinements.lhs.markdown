 {#simplerefinements}
=======================

Simple Refinement Types
-----------------------

<div class="hidden">


<pre><span class=hs-linenum>10: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-termination"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>11: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>SimpleRefinements</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>12: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span>
<span class=hs-linenum>13: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>abs</span><span class='hs-layout'>,</span> <span class='hs-varid'>max</span><span class='hs-layout'>)</span>
<span class=hs-linenum>14: </span>
<span class=hs-linenum>15: </span><span class='hs-comment'>-- boring haskell type sigs</span>
<span class=hs-linenum>16: </span><span class='hs-definition'>zero</span>    <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>17: </span><span class='hs-definition'>zero'</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>18: </span><span class='hs-definition'>safeDiv</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>19: </span><span class='hs-definition'>abs</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>20: </span><span class='hs-definition'>nats</span>    <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>21: </span><span class='hs-definition'>range</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-conid'>Int</span>
</pre>

</div>


Simple Refinement Types
=======================


Types + Predicates 
------------------


Example
-------

Integers equal to `0`

<br>


<pre><span class=hs-linenum>43: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>EqZero</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>


Example
-------

Integers equal to `0`

<br>


<pre><span class=hs-linenum>55: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>zero</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>EqZero</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>56: </span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV == 0)}</span><span class='hs-definition'>zero</span></a>     <span class='hs-keyglyph'>=</span>  <a class=annot href="#"><span class=annottext>x1:(GHC.Prim.Int#) -&gt; {x2 : (GHC.Types.Int) | (x2 == (x1  :  int))}</span><span class='hs-num'>0</span></a>
</pre>

<br>

<div class="fragment">
Refinement types via special comments `{-@ ... @-}`
</div>


<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo</a> 
Lets take a look.
</div>

 {#refinementsArePredicates}
============================

Refinements Are Predicates
--------------------------


Refinements Are Predicates
==========================

Subtyping is Implication
------------------------

[Predicate Subtyping](http://pvs.csl.sri.com/papers/subtypes98/tse98.pdf)


Subtyping is Implication
------------------------

<br>

--------  ---  ---------------------------------------------
  **If**   :   Refinement of `S` *implies* refinement of `T` 

**Then**   :   `S` is a *subtype* of `T`
--------  ---  ---------------------------------------------

<br>


Subtyping is Implication
------------------------


<br>

--------   ---     ----------------------------
  **If**    :      `p => q`
                
**Then**    :      `{v : t | p} <: {v : t | q}`
--------   ---     ----------------------------


Subtyping is Implication
------------------------

<br>

--------    ---  ---------------------------------------------------
  **As**     :   `v=0` *implies* `0<=v` ... via SMT
                 
  **So**     :   `{v:Int | v=0} <: {v:Int | 0<=v}`
--------    ---  ---------------------------------------------------


Example: Natural Numbers
------------------------

 . 
<pre><span class=hs-linenum>132: </span><span class='hs-keyword'>type</span> <span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-num'>0</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span>
</pre>

<br>

Via SMT, LiquidHaskell infers `EqZero <: Nat`, hence:

<br>


<pre><span class=hs-linenum>142: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>zero'</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Nat</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>143: </span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt;= 0)}</span><span class='hs-definition'>zero'</span></a>     <span class='hs-keyglyph'>=</span>  <a class=annot href="#"><span class=annottext>{x3 : (GHC.Types.Int) | (x3 == 0) &amp;&amp; (x3 == SimpleRefinements.zero)}</span><span class='hs-varid'>zero</span></a>
</pre>

 {#universalinvariants}
=======================

Types = Universal Invariants
----------------------------

(Notoriously hard with *pure* SMT)

Types Yield Universal Invariants
================================

Example: Lists
--------------

<div class="hidden">


<pre><span class=hs-linenum>163: </span><span class='hs-keyword'>infixr</span> <span class='hs-varop'>`C`</span>
</pre>

</div>

<br>


<pre><span class=hs-linenum>171: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>|</span> <span class='hs-conid'>C</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
</pre>

<br>

<div class="fragment">

*Every element* in `nats` is non-negative:

<br>


<pre><span class=hs-linenum>183: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>nats</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-conid'>Nat</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>184: </span><a class=annot href="#"><span class=annottext>(SimpleRefinements.L {VV : (GHC.Types.Int) | (VV &gt;= 0)})</span><span class='hs-definition'>nats</span></a>     <span class='hs-keyglyph'>=</span>  <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>{x14 : (GHC.Types.Int) | (x14 &gt;= 0) &amp;&amp; (x14 &gt;= SimpleRefinements.zero) &amp;&amp; (SimpleRefinements.zero &lt;= x14)}
-&gt; (SimpleRefinements.L {x14 : (GHC.Types.Int) | (x14 &gt;= 0) &amp;&amp; (x14 &gt;= SimpleRefinements.zero) &amp;&amp; (SimpleRefinements.zero &lt;= x14)})
-&gt; (SimpleRefinements.L {x14 : (GHC.Types.Int) | (x14 &gt;= 0) &amp;&amp; (x14 &gt;= SimpleRefinements.zero) &amp;&amp; (SimpleRefinements.zero &lt;= x14)})</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a> <a class=annot href="#"><span class=annottext>{x20 : (GHC.Types.Int) | (x20 /= 0) &amp;&amp; (x20 &gt; 0) &amp;&amp; (x20 &gt; SimpleRefinements.zero) &amp;&amp; (x20 &gt;= 0) &amp;&amp; (SimpleRefinements.zero &lt;= x20)}
-&gt; (SimpleRefinements.L {x20 : (GHC.Types.Int) | (x20 /= 0) &amp;&amp; (x20 &gt; 0) &amp;&amp; (x20 &gt; SimpleRefinements.zero) &amp;&amp; (x20 &gt;= 0) &amp;&amp; (SimpleRefinements.zero &lt;= x20)})
-&gt; (SimpleRefinements.L {x20 : (GHC.Types.Int) | (x20 /= 0) &amp;&amp; (x20 &gt; 0) &amp;&amp; (x20 &gt; SimpleRefinements.zero) &amp;&amp; (x20 &gt;= 0) &amp;&amp; (SimpleRefinements.zero &lt;= x20)})</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == (3  :  int))}</span><span class='hs-num'>3</span></a> <a class=annot href="#"><span class=annottext>{x20 : (GHC.Types.Int) | (x20 /= 0) &amp;&amp; (x20 &gt; 0) &amp;&amp; (x20 &gt; SimpleRefinements.zero) &amp;&amp; (x20 &gt;= 0) &amp;&amp; (SimpleRefinements.zero &lt;= x20)}
-&gt; (SimpleRefinements.L {x20 : (GHC.Types.Int) | (x20 /= 0) &amp;&amp; (x20 &gt; 0) &amp;&amp; (x20 &gt; SimpleRefinements.zero) &amp;&amp; (x20 &gt;= 0) &amp;&amp; (SimpleRefinements.zero &lt;= x20)})
-&gt; (SimpleRefinements.L {x20 : (GHC.Types.Int) | (x20 /= 0) &amp;&amp; (x20 &gt; 0) &amp;&amp; (x20 &gt; SimpleRefinements.zero) &amp;&amp; (x20 &gt;= 0) &amp;&amp; (SimpleRefinements.zero &lt;= x20)})</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>(SimpleRefinements.L {x2 : (GHC.Types.Int) | false})</span><span class='hs-conid'>N</span></a>
</pre>

</div>

<br>

<div class="fragment">

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo:</a> 
What if `nats` contained `-2`? 

</div>

 {#functiontypes}
=================

Contracts = Function Types
--------------------------

Contracts: Function Types
=========================


Example: `safeDiv`
------------------

<br>

**Precondition** divisor is *non-zero*.

<br>

<div class="fragment">

<pre><span class=hs-linenum>219: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>NonZero</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>/=</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>
</div>

<br>

Example: `safeDiv`
------------------

<br>

+ **Pre-condition** divisor is *non-zero*.
+ **Input type** specifies *pre-condition*

<br>


<pre><span class=hs-linenum>236: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>safeDiv</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>NonZero</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>237: </span><a class=annot href="#"><span class=annottext>(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV /= 0)} -&gt; (GHC.Types.Int)</span><span class='hs-definition'>safeDiv</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV /= 0)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int)
-&gt; {x6 : (GHC.Types.Int) | (((x1 &gt;= 0) &amp;&amp; (x2 &gt;= 0)) =&gt; (x6 &gt;= 0)) &amp;&amp; (((x1 &gt;= 0) &amp;&amp; (x2 &gt;= 1)) =&gt; (x6 &lt;= x1)) &amp;&amp; (x6 == (x1 / x2))}</span><span class='hs-varop'>`div`</span></a> <a class=annot href="#"><span class=annottext>{x3 : (GHC.Types.Int) | (x3 == y) &amp;&amp; (x3 /= 0)}</span><span class='hs-varid'>y</span></a>
</pre>

<br>

<div class="fragment">

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo:</a> 
What if precondition does not hold?

</div>

Example: `abs`
--------------

<br>

+ **Postcondition** result is non-negative
+ **Output type** specifies *post-condition*

<br>


<pre><span class=hs-linenum>260: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>abs</span>       <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Nat</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>261: </span><a class=annot href="#"><span class=annottext>(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV &gt;= 0)}</span><span class='hs-definition'>abs</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>x</span></a> 
<span class=hs-linenum>262: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int)
-&gt; {x2 : (GHC.Types.Bool) | (((Prop x2)) &lt;=&gt; (x1 &lt;= x2))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == x)}</span><span class='hs-varid'>x</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == x)}</span><span class='hs-varid'>x</span></a> 
<span class=hs-linenum>263: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int) -&gt; {x4 : (GHC.Types.Int) | (x4 == (x1 - x2))}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == x)}</span><span class='hs-varid'>x</span></a>
</pre>



 {#dependentfunctions}
======================

Dependent Function Types
------------------------

+ Outputs *refer to* inputs
+ *Relational* invariants


Dependent Function Types
========================

Example: `range`
----------------

`(range i j)` returns `Int`s between `i` and `j`


Example: `range`
----------------

`(range i j)` returns `Int`s between `i` and `j`

<br>


<pre><span class=hs-linenum>295: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>Btwn</span> <span class='hs-conid'>I</span> <span class='hs-conid'>J</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span><span class='hs-keyglyph'>|</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&lt;</span> <span class='hs-conid'>J</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

Example: `range`
----------------

`(range i j)` returns `Int`s between `i` and `j`

<br>


<pre><span class=hs-linenum>306: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>range</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-layout'>(</span><span class='hs-conid'>Btwn</span> <span class='hs-varid'>i</span> <span class='hs-varid'>j</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>307: </span><a class=annot href="#"><span class=annottext>i:(GHC.Types.Int)
-&gt; j:(GHC.Types.Int)
-&gt; (SimpleRefinements.L {v : (GHC.Types.Int) | (v &lt; j) &amp;&amp; (i &lt;= v)})</span><span class='hs-definition'>range</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>j</span></a>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x10 : (GHC.Types.Int) | (x10 &gt;= i) &amp;&amp; (i &lt;= x10)}
-&gt; (SimpleRefinements.L {x7 : (GHC.Types.Int) | (x7 &gt;= i) &amp;&amp; (x7 &gt;= x1) &amp;&amp; (x7 &lt; j) &amp;&amp; (i &lt;= x7) &amp;&amp; (x1 &lt;= x7)})</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == i)}</span><span class='hs-varid'>i</span></a>
<span class=hs-linenum>308: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>309: </span>    <a class=annot href="#"><span class=annottext>n:{VV : (GHC.Types.Int) | (VV &gt;= i) &amp;&amp; (i &lt;= VV)}
-&gt; (SimpleRefinements.L {VV : (GHC.Types.Int) | (VV &gt;= i) &amp;&amp; (VV &gt;= n) &amp;&amp; (VV &lt; j) &amp;&amp; (i &lt;= VV) &amp;&amp; (n &lt;= VV)})</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt;= i) &amp;&amp; (i &lt;= VV)}</span><span class='hs-varid'>n</span></a>
<span class=hs-linenum>310: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x4 : (GHC.Types.Int) | (x4 == n) &amp;&amp; (x4 &gt;= i) &amp;&amp; (i &lt;= x4)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int)
-&gt; {x2 : (GHC.Types.Bool) | (((Prop x2)) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == j)}</span><span class='hs-varid'>j</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x4 : (GHC.Types.Int) | (x4 == n) &amp;&amp; (x4 &gt;= i) &amp;&amp; (i &lt;= x4)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>{x20 : (GHC.Types.Int) | (x20 &gt;= i) &amp;&amp; (x20 &gt;= n) &amp;&amp; (x20 &lt; j) &amp;&amp; (i &lt;= x20) &amp;&amp; (n &lt;= x20)}
-&gt; (SimpleRefinements.L {x20 : (GHC.Types.Int) | (x20 &gt;= i) &amp;&amp; (x20 &gt;= n) &amp;&amp; (x20 &lt; j) &amp;&amp; (i &lt;= x20) &amp;&amp; (n &lt;= x20)})
-&gt; (SimpleRefinements.L {x20 : (GHC.Types.Int) | (x20 &gt;= i) &amp;&amp; (x20 &gt;= n) &amp;&amp; (x20 &lt; j) &amp;&amp; (i &lt;= x20) &amp;&amp; (n &lt;= x20)})</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>n:{VV : (GHC.Types.Int) | (VV &gt;= i) &amp;&amp; (i &lt;= VV)}
-&gt; (SimpleRefinements.L {VV : (GHC.Types.Int) | (VV &gt;= i) &amp;&amp; (VV &gt;= n) &amp;&amp; (VV &lt; j) &amp;&amp; (i &lt;= VV) &amp;&amp; (n &lt;= VV)})</span><span class='hs-varid'>go</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x4 : (GHC.Types.Int) | (x4 == n) &amp;&amp; (x4 &gt;= i) &amp;&amp; (i &lt;= x4)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int) -&gt; {x4 : (GHC.Types.Int) | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span>  
<span class=hs-linenum>311: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(SimpleRefinements.L {x2 : (GHC.Types.Int) | false})</span><span class='hs-conid'>N</span></a>
</pre>

<br>

<div class="fragment">
**Question:** What is the type of `go` ?
</div>


Example: Indexing Into List
---------------------------

 
<pre><span class=hs-linenum>325: </span><span class='hs-layout'>(</span><span class='hs-varop'>!</span><span class='hs-layout'>)</span>          <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>326: </span><span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-keyword'>_</span><span class='hs-layout'>)</span>  <a class=annot href="#"><span class=annottext>forall a. (SimpleRefinements.L a) -&gt; (GHC.Types.Int) -&gt; a</span><span class='hs-varop'>!</span></a> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>327: </span><span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-keyword'>_</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varop'>!</span> <span class='hs-varid'>i</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(SimpleRefinements.L a)</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>(SimpleRefinements.L a) -&gt; (GHC.Types.Int) -&gt; a</span><span class='hs-varop'>!</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int) -&gt; {x4 : (GHC.Types.Int) | (x4 == (x1 - x2))}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>328: </span><span class='hs-keyword'>_</span>        <span class='hs-varop'>!</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x1 : [(GHC.Types.Char)] | false} -&gt; {VV : a | false}</span><span class='hs-varid'>liquidError</span></a> <span class=hs-error><a class=annot href="#"><span class=annottext>{x3 : [(GHC.Types.Char)] | ((len x3) &gt;= 0) &amp;&amp; ((sumLens x3) &gt;= 0)}</span><span class='hs-str'>"Oops!"</span></a></span>
</pre>

<br>

<div class="fragment">(Mouseover to view type of `liquidError`)</div>

<br>

- <div class="fragment">**Q:** How to ensure safety? </div>
- <div class="fragment">**A:** Precondition: `i` between `0` and list **length**.

<div class="fragment">Need way to [measure](#measures) *length of a list* ...</div>


