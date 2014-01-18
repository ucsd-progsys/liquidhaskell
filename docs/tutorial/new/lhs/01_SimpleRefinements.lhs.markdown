 {#simplerefinements}
=======================

Simple Refinement Types
-----------------------

<div class="hidden">


<pre><span class=hs-linenum>10: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>SimpleRefinements</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>11: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span>
<span class=hs-linenum>12: </span>
<span class=hs-linenum>13: </span><span class='hs-comment'>-- boring haskell type sigs</span>
<span class=hs-linenum>14: </span><span class='hs-definition'>zero</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
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


<pre><span class=hs-linenum>36: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>EqZero</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>


Example
-------

Integers equal to `0`

<br>


<pre><span class=hs-linenum>48: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>zero</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>{v :</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = 0}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>49: </span><a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == 0)}</span><span class='hs-definition'>zero</span></a>     <span class='hs-keyglyph'>=</span>  <a class=annot href="#"><span class=annottext>x1:(GHC.Prim.Int#) -&gt; {x2 : (GHC.Types.Int) | (x2 == (x1  :  int))}</span><span class='hs-num'>0</span></a>
</pre>

<br>

<div class="fragment">
Refinement types via special comments
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

--------    ----------------------------
  **If**    `p => q`

**Then**    `{v : t | p} <: {v : t | q}`
--------    ----------------------------


Subtyping is Implication
------------------------

<br>

--------  ---------------------------------
  **As**  `v=0` *implies* `0<=v`

  **So**  `{v:Int | v=0} <: {v:Int | 0<=v}`
--------  ---------------------------------


Example: Natural Numbers
------------------------

<br>

 &nbsp;
<pre><span class=hs-linenum>127: </span><span class='hs-keyword'>type</span> <span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-num'>0</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span>
</pre>

<br>

And, via SMT based subtyping LiquidHaskell verifies:

<br>


<pre><span class=hs-linenum>137: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>zero'</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Nat</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>138: </span><span class='hs-definition'>zero'</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>139: </span><a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 &gt;= 0)}</span><span class='hs-definition'>zero'</span></a>     <span class='hs-keyglyph'>=</span>  <a class=annot href="#"><span class=annottext>x1:(GHC.Prim.Int#) -&gt; {x2 : (GHC.Types.Int) | (x2 == (x1  :  int))}</span><span class='hs-num'>0</span></a>
</pre>


Lists: Universal Invariants 
---------------------------

Constructors enable *universally quantified* invariants.

For example, we define a list:


<pre><span class=hs-linenum>151: </span><span class='hs-keyword'>infixr</span> <span class='hs-varop'>`C`</span>
<span class=hs-linenum>152: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>|</span> <span class='hs-conid'>C</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
</pre>

<br>

And specify that, *every element* in a list is non-negative:


<pre><span class=hs-linenum>160: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>natList</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-conid'>Nat</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>161: </span><span class='hs-definition'>natList</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>162: </span><a class=annot href="#"><span class=annottext>(SimpleRefinements.L {x3 : (GHC.Types.Int) | (x3 &gt;= 0)})</span><span class='hs-definition'>natList</span></a>     <span class='hs-keyglyph'>=</span>  <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>{x11 : (GHC.Types.Int) | (x11 &gt;= 0) &amp;&amp; (x11 &gt;= SimpleRefinements.zero)}
-&gt; (SimpleRefinements.L {x11 : (GHC.Types.Int) | (x11 &gt;= 0) &amp;&amp; (x11 &gt;= SimpleRefinements.zero)})
-&gt; (SimpleRefinements.L {x11 : (GHC.Types.Int) | (x11 &gt;= 0) &amp;&amp; (x11 &gt;= SimpleRefinements.zero)})</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a> <a class=annot href="#"><span class=annottext>{x17 : (GHC.Types.Int) | (x17 /= 0) &amp;&amp; (x17 &gt; 0) &amp;&amp; (x17 &gt; SimpleRefinements.zero) &amp;&amp; (x17 &gt;= 0)}
-&gt; (SimpleRefinements.L {x17 : (GHC.Types.Int) | (x17 /= 0) &amp;&amp; (x17 &gt; 0) &amp;&amp; (x17 &gt; SimpleRefinements.zero) &amp;&amp; (x17 &gt;= 0)})
-&gt; (SimpleRefinements.L {x17 : (GHC.Types.Int) | (x17 /= 0) &amp;&amp; (x17 &gt; 0) &amp;&amp; (x17 &gt; SimpleRefinements.zero) &amp;&amp; (x17 &gt;= 0)})</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == (3  :  int))}</span><span class='hs-num'>3</span></a> <a class=annot href="#"><span class=annottext>{x17 : (GHC.Types.Int) | (x17 /= 0) &amp;&amp; (x17 &gt; 0) &amp;&amp; (x17 &gt; SimpleRefinements.zero) &amp;&amp; (x17 &gt;= 0)}
-&gt; (SimpleRefinements.L {x17 : (GHC.Types.Int) | (x17 /= 0) &amp;&amp; (x17 &gt; 0) &amp;&amp; (x17 &gt; SimpleRefinements.zero) &amp;&amp; (x17 &gt;= 0)})
-&gt; (SimpleRefinements.L {x17 : (GHC.Types.Int) | (x17 /= 0) &amp;&amp; (x17 &gt; 0) &amp;&amp; (x17 &gt; SimpleRefinements.zero) &amp;&amp; (x17 &gt;= 0)})</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>(SimpleRefinements.L {x2 : (GHC.Types.Int) | false})</span><span class='hs-conid'>N</span></a>
</pre>

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo:</a> 
Lets see what happens if `natList` contained a negative number. 

Refinement Function Types
-------------------------

Consider a `safeDiv` operator: <br>


<pre><span class=hs-linenum>174: </span><span class='hs-definition'>safeDiv</span>    <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>175: </span><a class=annot href="#"><span class=annottext>(GHC.Types.Int)
-&gt; {x3 : (GHC.Types.Int) | (x3 /= 0)} -&gt; (GHC.Types.Int)</span><span class='hs-definition'>safeDiv</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 /= 0)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : (GHC.Types.Int) | (x2 == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:(GHC.Types.Int)
-&gt; x2:(GHC.Types.Int)
-&gt; {x6 : (GHC.Types.Int) | (((x1 &gt;= 0) &amp;&amp; (x2 &gt;= 0)) =&gt; (x6 &gt;= 0)) &amp;&amp; (((x1 &gt;= 0) &amp;&amp; (x2 &gt;= 1)) =&gt; (x6 &lt;= x1)) &amp;&amp; (x6 == (x1 / x2))}</span><span class='hs-varop'>`div`</span></a> <a class=annot href="#"><span class=annottext>{x3 : (GHC.Types.Int) | (x3 == y) &amp;&amp; (x3 /= 0)}</span><span class='hs-varid'>y</span></a>
</pre>

<br>
We can use refinements to specify a **precondition**: divisor is **non-zero** <br>


<pre><span class=hs-linenum>182: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>safeDiv</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v != 0}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
</pre>

<br>

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo:</a> 
Lets see what happens if the preconditions cannot be
proven. 

Dependent Function Types
------------------------

 Consider a list indexing function:
<pre><span class=hs-linenum>195: </span><span class='hs-layout'>(</span><span class='hs-varop'>!!</span><span class='hs-layout'>)</span>         <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>196: </span><span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-varid'>x</span> <span class='hs-keyword'>_</span><span class='hs-layout'>)</span> <span class='hs-varop'>!!</span> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>x</span>
<span class=hs-linenum>197: </span><span class='hs-layout'>(</span><span class='hs-conid'>C</span> <span class='hs-keyword'>_</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-varop'>!!</span> <span class='hs-varid'>n</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>xs</span><span class='hs-varop'>!!</span><span class='hs-layout'>(</span><span class='hs-varid'>n</span><span class='hs-comment'>-</span><span class='hs-num'>1</span><span class='hs-layout'>)</span>
<span class=hs-linenum>198: </span><span class='hs-keyword'>_</span>       <span class='hs-varop'>!!</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>liquidError</span> <span class='hs-str'>"This should not happen!"</span>
</pre>

<br>

We desire a **precondition** that index `i` be between `0` and **list length**.

We use **measures** to talk about the length of a list in **logic**.


