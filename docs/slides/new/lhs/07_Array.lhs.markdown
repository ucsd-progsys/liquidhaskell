Abstract Refinements {#data}
============================

Recap
-----

**So far**

Decouple invariants from *functions*

<br>

<div class="fragment">

**Next**

Decouple invariants from *data structures*
</div>

Decouple Invariants From Data {#vector} 
=======================================

Example: Vectors 
----------------

<div class="hidden">

<pre><span class=hs-linenum>28: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>LiquidArray</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>29: </span>
<span class=hs-linenum>30: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span> <span class='hs-layout'>(</span><span class='hs-varid'>liquidAssume</span><span class='hs-layout'>,</span> <span class='hs-varid'>liquidError</span><span class='hs-layout'>)</span>
<span class=hs-linenum>31: </span>
<span class=hs-linenum>32: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-termination"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>33: </span>
<span class=hs-linenum>34: </span><span class='hs-definition'>fibMemo</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Vec</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Vec</span> <span class='hs-conid'>Int</span><span class='hs-layout'>,</span> <span class='hs-conid'>Int</span><span class='hs-layout'>)</span>
<span class=hs-linenum>35: </span><span class='hs-definition'>fastFib</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>36: </span><span class='hs-definition'>idv</span>       <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Vec</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>37: </span><span class='hs-definition'>axiom_fib</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>38: </span><a class=annot href="#"><span class=annottext>i:(Int)
-&gt; {v : (Bool) | (((Prop v)) &lt;=&gt; ((fib i) == (if (i &lt;= 1) then 1 else ((fib (i - 1)) + (fib (i - 2))))))}</span><span class='hs-definition'>axiom_fib</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a. a</span><span class='hs-varid'>undefined</span></a>
<span class=hs-linenum>39: </span>
<span class=hs-linenum>40: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>AxFib</span> <span class='hs-conid'>I</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>fib</span> <span class='hs-conid'>I</span><span class='hs-layout'>)</span> <span class='hs-varop'>==</span> <span class='hs-layout'>(</span><span class='hs-keyword'>if</span> <span class='hs-conid'>I</span> <span class='hs-varop'>&lt;=</span> <span class='hs-num'>1</span> <span class='hs-keyword'>then</span> <span class='hs-num'>1</span> <span class='hs-keyword'>else</span> <span class='hs-varid'>fib</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span><span class='hs-comment'>-</span><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varop'>+</span> <span class='hs-varid'>fib</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span><span class='hs-comment'>-</span><span class='hs-num'>2</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>
</div>

<div class="fragment">

Implemented as maps from `Int` to `a` 

<br>


<pre><span class=hs-linenum>51: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>V</span> <span class='hs-layout'>(</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
</pre>

</div>


Abstract *Domain* and *Range*
-----------------------------

Parameterize type with *two* abstract refinements:

<br>


<pre><span class=hs-linenum>65: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>dom</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-layout'>,</span>
<span class=hs-linenum>66: </span>                 <span class='hs-varid'>rng</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span> <span class='hs-varop'>&gt;</span>
<span class=hs-linenum>67: </span>      <span class='hs-keyglyph'>=</span> <span class='hs-conid'>V</span> <span class='hs-layout'>{</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>dom</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>rng</span> <span class='hs-varid'>i</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>}</span>  <span class='hs-keyword'>@-}</span>
</pre>

<br>

- `dom`: *domain* on which `Vec` is *defined* 

- `rng`: *range*  and relationship with *index*

Abstract *Domain* and *Range*
-----------------------------

Diverse `Vec`tors by *instantiating* `dom` and `rng`

<br>

<div class="fragment">

A quick alias for *segments* between `I` and `J`

<br>


<pre><span class=hs-linenum>90: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>Seg</span> <span class='hs-conid'>V</span> <span class='hs-conid'>I</span> <span class='hs-conid'>J</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varop'>&lt;=</span> <span class='hs-conid'>V</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-conid'>V</span> <span class='hs-varop'>&lt;</span> <span class='hs-conid'>J</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>

</div>

Ex: Identity Vectors
--------------------

Defined between `[0..N)` mapping each key to itself:

<br>

<div class="fragment">


<pre><span class=hs-linenum>105: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>IdVec</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Vec</span> <span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Seg</span> <span class='hs-varid'>v</span> <span class='hs-num'>0</span> <span class='hs-conid'>N</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span><span class='hs-layout'>,</span> 
<span class=hs-linenum>106: </span>                        <span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>k</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>v</span><span class='hs-keyglyph'>=</span><span class='hs-varid'>k</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>107: </span>                       <span class='hs-conid'>Int</span>                  <span class='hs-keyword'>@-}</span>
</pre>

</div>

Ex: Identity Vectors
--------------------

Defined between `[0..N)` mapping each key to itself:

<br>


<pre><span class=hs-linenum>120: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>idv</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>IdVec</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>121: </span><a class=annot href="#"><span class=annottext>n:{VV : (Int) | (VV &gt;= 0)}
-&gt; (Vec &lt;(VV &lt; n) &amp;&amp; (0 &lt;= VV), \k4 VV -&gt; (VV == k4)&gt; (Int))</span><span class='hs-definition'>idv</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0)}</span><span class='hs-varid'>n</span></a>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;rng :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool, dom :: (GHC.Types.Int)-&gt; Bool&gt;.
(i:{x13 : (Int)&lt;dom&gt; | true}
 -&gt; {x12 : (Int)&lt;rng i&gt; | (x12 &gt; 0) &amp;&amp; (x12 &gt;= 0) &amp;&amp; (x12 &lt; n)})
-&gt; (Vec &lt;dom, rng&gt; {x12 : (Int) | (x12 &gt; 0) &amp;&amp; (x12 &gt;= 0) &amp;&amp; (x12 &lt; n)})</span><span class='hs-conid'>V</span></a> <span class='hs-layout'>(</span><span class='hs-keyglyph'>\</span><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; n)}</span><span class='hs-varid'>k</span></a> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>if</span> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x1:{x12 : (Int) | (x12 &gt;= 0) &amp;&amp; (x12 &lt; n) &amp;&amp; (0 &lt;= x12) &amp;&amp; (x12 &lt;= k)}
-&gt; x2:{x12 : (Int) | (x12 &gt;= 0) &amp;&amp; (x12 &lt; n) &amp;&amp; (0 &lt;= x12) &amp;&amp; (x12 &lt;= k)}
-&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{x4 : (Int) | (x4 == k) &amp;&amp; (x4 &gt;= 0) &amp;&amp; (x4 &lt; n)}</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>x1:(Bool)
-&gt; x2:(Bool)
-&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (((Prop x1)) &amp;&amp; ((Prop x2))))}</span><span class='hs-varop'>&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>{x4 : (Int) | (x4 == k) &amp;&amp; (x4 &gt;= 0) &amp;&amp; (x4 &lt; n)}</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>x1:{x12 : (Int) | (x12 &gt;= 0) &amp;&amp; (x12 &gt;= k) &amp;&amp; (0 &lt;= x12) &amp;&amp; (x12 &lt;= n)}
-&gt; x2:{x12 : (Int) | (x12 &gt;= 0) &amp;&amp; (x12 &gt;= k) &amp;&amp; (0 &lt;= x12) &amp;&amp; (x12 &lt;= n)}
-&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == n) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>n</span></a> 
<span class=hs-linenum>122: </span>                     <span class='hs-keyword'>then</span> <a class=annot href="#"><span class=annottext>{x4 : (Int) | (x4 == k) &amp;&amp; (x4 &gt;= 0) &amp;&amp; (x4 &lt; n)}</span><span class='hs-varid'>k</span></a> 
<span class=hs-linenum>123: </span>                     <span class='hs-keyword'>else</span> <a class=annot href="#"><span class=annottext>{x2 : [(Char)] | false} -&gt; {x1 : (Int) | false}</span><span class='hs-varid'>liquidError</span></a> <span class=hs-error><a class=annot href="#"><span class=annottext>{x3 : [(Char)] | ((len x3) &gt;= 0) &amp;&amp; ((sumLens x3) &gt;= 0)}</span><span class='hs-str'>"eeks"</span></a></span><span class='hs-layout'>)</span>
</pre>

<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=Array.hs" target="_blank">Demo:</a>Whats the problem? How can we fix it?
</div>

Ex: Zero-Terminated Vectors
---------------------------

Defined between `[0..N)`, with *last* element equal to `0`:

<br>

<div class="fragment">


<pre><span class=hs-linenum>142: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>ZeroTerm</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> 
<span class=hs-linenum>143: </span>     <span class='hs-conid'>Vec</span> <span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Seg</span> <span class='hs-varid'>v</span> <span class='hs-num'>0</span> <span class='hs-conid'>N</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span><span class='hs-layout'>,</span> 
<span class=hs-linenum>144: </span>          <span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>k</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>k</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span><span class='hs-comment'>-</span><span class='hs-num'>1</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>145: </span>          <span class='hs-conid'>Int</span>                             <span class='hs-keyword'>@-}</span>
</pre>

</div>


Ex: Fibonacci Table 
-------------------

A vector whose value at index `k` is either 

- `0` (undefined), or, 

- `k`th fibonacci number 


<pre><span class=hs-linenum>161: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>FibV</span> <span class='hs-keyglyph'>=</span>  
<span class=hs-linenum>162: </span>     <span class='hs-conid'>Vec</span> <span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>true</span><span class='hs-layout'>}</span><span class='hs-layout'>,</span> 
<span class=hs-linenum>163: </span>          <span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>k</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span> <span class='hs-varop'>||</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>fib</span> <span class='hs-varid'>k</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>164: </span>          <span class='hs-conid'>Int</span>                               <span class='hs-keyword'>@-}</span>
</pre>


Accessing Vectors
-----------------

Next: lets *abstractly* type `Vec`tor operations, *e.g.* 

<br>

- `empty`

- `set`

- `get`


Ex: Empty Vectors
-----------------

`empty` returns Vector whose domain is `false`

<br>


<pre><span class=hs-linenum>190: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>empty</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> 
<span class=hs-linenum>191: </span>               <span class='hs-conid'>Vec</span> <span class='hs-varop'>&lt;</span><span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span><span class='hs-keyword'>|false}</span><span class='hs-layout'>,</span> <span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>a</span>     <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>192: </span>
<span class=hs-linenum>193: </span><a class=annot href="#"><span class=annottext>forall a &lt;p :: (GHC.Types.Int)-&gt; a-&gt; Bool&gt;.
(Vec &lt;false, \_ VV -&gt; p&gt; a)</span><span class='hs-definition'>empty</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>({x4 : (Int) | false} -&gt; {VV : a | false})
-&gt; (Vec &lt;false, \_ VV -&gt; false&gt; {VV : a | false})</span><span class='hs-conid'>V</span></a> <a class=annot href="#"><span class=annottext>(({x9 : (Int) | false} -&gt; {VV : a | false})
 -&gt; (Vec &lt;false, \_ VV -&gt; false&gt; {VV : a | false}))
-&gt; ({x9 : (Int) | false} -&gt; {VV : a | false})
-&gt; (Vec &lt;false, \_ VV -&gt; false&gt; {VV : a | false})</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>{x1 : (Int) | false} -&gt; {VV : a | false}</span><span class='hs-keyglyph'>\</span></a><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>[(Char)] -&gt; {VV : a | false}</span><span class='hs-varid'>error</span></a> <a class=annot href="#"><span class=annottext>{x3 : [(Char)] | ((len x3) &gt;= 0) &amp;&amp; ((sumLens x3) &gt;= 0)}</span><span class='hs-str'>"empty vector!"</span></a>
</pre>

<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=Array.hs" target="_blank">Demo:</a>
What would happen if we changed `false` to `true`?
</div>

Ex: `get` Key's Value 
---------------------

- *Input* `key` in *domain*

- *Output* value in *range* related with `k`


<pre><span class=hs-linenum>211: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>get</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>d</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-layout'>,</span>  
<span class=hs-linenum>212: </span>                     <span class='hs-varid'>r</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span>
<span class=hs-linenum>213: </span>           <span class='hs-varid'>key</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>d</span><span class='hs-varop'>&gt;</span>
<span class=hs-linenum>214: </span>        <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>vec</span><span class='hs-conop'>:</span><span class='hs-conid'>Vec</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>d</span><span class='hs-layout'>,</span> <span class='hs-varid'>r</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>215: </span>        <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>r</span> <span class='hs-varid'>key</span><span class='hs-varop'>&gt;</span>                        <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>216: </span>
<span class=hs-linenum>217: </span><a class=annot href="#"><span class=annottext>forall a &lt;d :: (GHC.Types.Int)-&gt; Bool, r :: (GHC.Types.Int)-&gt; a-&gt; Bool&gt;.
key:{VV : (Int)&lt;d&gt; | true}
-&gt; (Vec &lt;d, \_ VV -&gt; r&gt; a) -&gt; {VV : a&lt;r key&gt; | true}</span><span class='hs-definition'>get</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((papp1 d VV))}</span><span class='hs-varid'>k</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>V</span> <span class='hs-varid'>f</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x2 : (Int) | ((papp1 d x2))} -&gt; {VV : a | ((papp2 r VV x1))}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Int) | ((papp1 d x3)) &amp;&amp; (x3 == k)}</span><span class='hs-varid'>k</span></a>
</pre>


Ex: `set` Key's Value 
---------------------

- <div class="fragment">Input `key` in *domain*</div>

- <div class="fragment">Input `val` in *range* related with `key`</div>

- <div class="fragment">Input `vec` defined at *domain except at* `key`</div>

- <div class="fragment">Output domain *includes* `key`</div>

Ex: `set` Key's Value 
---------------------


<pre><span class=hs-linenum>236: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>set</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>d</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-layout'>,</span>
<span class=hs-linenum>237: </span>                     <span class='hs-varid'>r</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span>
<span class=hs-linenum>238: </span>           <span class='hs-varid'>key</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>d</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>val</span><span class='hs-conop'>:</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>r</span> <span class='hs-varid'>key</span><span class='hs-varop'>&gt;</span>
<span class=hs-linenum>239: </span>        <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>vec</span><span class='hs-conop'>:</span> <span class='hs-conid'>Vec</span><span class='hs-varop'>&lt;</span><span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>d</span><span class='hs-varop'>&gt;</span><span class='hs-keyword'>| v /= key}</span><span class='hs-layout'>,</span><span class='hs-varid'>r</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>240: </span>        <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Vec</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>d</span><span class='hs-layout'>,</span> <span class='hs-varid'>r</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>a</span>                     <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>241: </span><a class=annot href="#"><span class=annottext>forall a &lt;d :: (GHC.Types.Int)-&gt; Bool, r :: (GHC.Types.Int)-&gt; a-&gt; Bool&gt;.
key:{VV : (Int)&lt;d&gt; | true}
-&gt; {VV : a&lt;r key&gt; | true}
-&gt; (Vec &lt;d &amp; (VV /= key), \_ VV -&gt; r&gt; a)
-&gt; (Vec &lt;d, \_ VV -&gt; r&gt; a)</span><span class='hs-definition'>set</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((papp1 d VV))}</span><span class='hs-varid'>key</span></a> <a class=annot href="#"><span class=annottext>{VV : a | ((papp2 r VV key))}</span><span class='hs-varid'>val</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>V</span> <span class='hs-varid'>f</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>({x6 : (Int) | ((papp1 d x6))} -&gt; {VV : a | ((papp2 r VV key))})
-&gt; (Vec &lt;((papp1 d x3)), \_ VV -&gt; ((papp2 r VV key))&gt; {VV : a | ((papp2 r VV key))})</span><span class='hs-conid'>V</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>(({x13 : (Int) | ((papp1 d x13))} -&gt; {VV : a | ((papp2 r VV key))})
 -&gt; (Vec &lt;((papp1 d x10)), \_ VV -&gt; ((papp2 r VV key))&gt; {VV : a | ((papp2 r VV key))}))
-&gt; ({x13 : (Int) | ((papp1 d x13))}
    -&gt; {VV : a | ((papp2 r VV key))})
-&gt; (Vec &lt;((papp1 d x10)), \_ VV -&gt; ((papp2 r VV key))&gt; {VV : a | ((papp2 r VV key))})</span><span class='hs-varop'>$</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-keyglyph'>\</span></span><span class=hs-error><a class=annot href="#"><span class=annottext>{VV : (Int) | ((papp1 d VV))}</span><span class='hs-varid'>k</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-keyglyph'>-&gt;</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-keyword'>if</span></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{x3 : (Int) | ((papp1 d x3)) &amp;&amp; (x3 == k)}</span><span class='hs-varid'>k</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>x1:{x6 : (Int) | ((papp1 d x6))}
-&gt; x2:{x6 : (Int) | ((papp1 d x6))}
-&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 == x2))}</span><span class='hs-varop'>==</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{x3 : (Int) | ((papp1 d x3)) &amp;&amp; (x3 == key)}</span><span class='hs-varid'>key</span></a></span><span class=hs-error> </span>
<span class=hs-linenum>242: </span>                                <span class=hs-error><span class='hs-keyword'>then</span></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{VV : a | ((papp2 r VV key)) &amp;&amp; (VV == val)}</span><span class='hs-varid'>val</span></a></span><span class=hs-error> </span><span class=hs-error>
</span><span class=hs-linenum>243: </span>                                <span class=hs-error><span class='hs-keyword'>else</span></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>x1:{x3 : (Int) | ((papp1 d x3)) &amp;&amp; (x3 /= key)}
-&gt; {VV : a | ((papp2 r VV x1))}</span><span class='hs-varid'>f</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{x3 : (Int) | ((papp1 d x3)) &amp;&amp; (x3 == key)}</span><span class='hs-varid'>key</span></a></span>
</pre>

<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=Array.hs" target="_blank">Demo:</a>
Help! Can you spot and fix the errors? 
</div>

<!-- INSERT tests/pos/vecloop.lhs here AFTER FIXED -->

Using the Vector API
--------------------

Memoized Fibonacci
------------------

Use `Vec` API to write a *memoized* fibonacci function

<br>

<div class="fragment">
 Using the fibonacci table:
<pre><span class=hs-linenum>267: </span><span class='hs-keyword'>type</span> <span class='hs-conid'>FibV</span> <span class='hs-keyglyph'>=</span>  
<span class=hs-linenum>268: </span>     <span class='hs-conid'>Vec</span> <span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>true</span><span class='hs-layout'>}</span><span class='hs-layout'>,</span> 
<span class=hs-linenum>269: </span>          <span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>k</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span> <span class='hs-varop'>||</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>fib</span> <span class='hs-varid'>k</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>270: </span>          <span class='hs-conid'>Int</span>                              
</pre>
</div>

<br>

<div class="fragment">
But wait, what is `fib` ?
</div>


Specifying Fibonacci
--------------------

`fib` is *uninterpreted* in the refinement logic  

<br>


<pre><span class=hs-linenum>289: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>fib</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
</pre>

<br>

Specifying Fibonacci
--------------------

We *axiomatize* the definition of `fib` in SMT ...

<br>
<pre><span class=hs-linenum>300: </span><span class='hs-definition'>predicate</span> <span class='hs-conid'>AxFib</span> <span class='hs-conid'>I</span> <span class='hs-keyglyph'>=</span> 
<span class=hs-linenum>301: </span>  <span class='hs-layout'>(</span><span class='hs-varid'>fib</span> <span class='hs-conid'>I</span><span class='hs-layout'>)</span> <span class='hs-varop'>==</span> <span class='hs-keyword'>if</span> <span class='hs-conid'>I</span> <span class='hs-varop'>&lt;=</span> <span class='hs-num'>1</span> 
<span class=hs-linenum>302: </span>               <span class='hs-keyword'>then</span> <span class='hs-num'>1</span> 
<span class=hs-linenum>303: </span>               <span class='hs-keyword'>else</span> <span class='hs-varid'>fib</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span><span class='hs-comment'>-</span><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varop'>+</span> <span class='hs-varid'>fib</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span><span class='hs-comment'>-</span><span class='hs-num'>2</span><span class='hs-layout'>)</span>
</pre>

Specifying Fibonacci
--------------------

Finally, lift axiom into LiquidHaskell as *ghost function*

<br>


<pre><span class=hs-linenum>314: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>axiom_fib</span> <span class='hs-keyglyph'>::</span> 
<span class=hs-linenum>315: </span>      <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyword'>_</span><span class='hs-keyword'>|((Prop v) &lt;=&gt; (AxFib i))}</span> <span class='hs-keyword'>@-}</span>
</pre>

<br>

<div class="fragment">
**Note:** Recipe for *escaping* SMT limitations

1. *Prove* fact externally
2. *Use* as ghost function call
</div>


Fast Fibonacci
--------------

An efficient fibonacci function

<br>


<pre><span class=hs-linenum>336: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fastFib</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyword'>_</span> <span class='hs-keyword'>| v = (fib n)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>337: </span><a class=annot href="#"><span class=annottext>n:(Int) -&gt; {v : (Int) | (v == (fib n))}</span><span class='hs-definition'>fastFib</span></a> <a class=annot href="#"><span class=annottext>(Int)</span><span class='hs-varid'>n</span></a>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>((Vec &lt;false, \x10 VV -&gt; ((x9 == 0) || (x9 == (fib x10)))&gt; (Int)), {x13 : (Int) | (x13 == (fib n))})
-&gt; {x2 : (Int) | (x2 == (fib n))}</span><span class='hs-varid'>snd</span></a> <a class=annot href="#"><span class=annottext>(((Vec &lt;false, \x24 VV -&gt; ((x23 == 0) || (x23 == (fib x24)))&gt; (Int)), {x27 : (Int) | (x27 == (fib n))})
 -&gt; {x16 : (Int) | (x16 == (fib n))})
-&gt; ((Vec &lt;false, \x24 VV -&gt; ((x23 == 0) || (x23 == (fib x24)))&gt; (Int)), {x27 : (Int) | (x27 == (fib n))})
-&gt; {x16 : (Int) | (x16 == (fib n))}</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>(Vec &lt;True, \x18 VV -&gt; ((x17 == 0) || (x17 == (fib x18)))&gt; (Int))
-&gt; x2:(Int)
-&gt; ((Vec &lt;True, \x8 VV -&gt; ((x7 == 0) || (x7 == (fib x8)))&gt; (Int)), {x11 : (Int) | (x11 == (fib x2))})</span><span class='hs-varid'>fibMemo</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall &lt;rng :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool, dom :: (GHC.Types.Int)-&gt; Bool&gt;.
(i:{x15 : (Int)&lt;dom&gt; | true}
 -&gt; {x14 : (Int)&lt;rng i&gt; | ((x14 == 0) || (x14 == (fib n))) &amp;&amp; (x14 == 0) &amp;&amp; (x14 &gt;= 0)})
-&gt; (Vec &lt;dom, rng&gt; {x14 : (Int) | ((x14 == 0) || (x14 == (fib n))) &amp;&amp; (x14 == 0) &amp;&amp; (x14 &gt;= 0)})</span><span class='hs-conid'>V</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(Int) -&gt; {x2 : (Int) | (x2 == (0  :  int))}</span><span class='hs-keyglyph'>\</span></a><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == n)}</span><span class='hs-varid'>n</span></a>
</pre>

<br>

<div class="fragment">
- `fibMemo` *takes* a table initialized with `0`

- `fibMemo` *returns* a table with `fib` values upto `n`.
</div>


Memoized Fibonacci 
------------------


<pre><span class=hs-linenum>353: </span><a class=annot href="#"><span class=annottext>(Vec &lt;True, \k10 VV -&gt; ((VV == 0) || (VV == (fib k10)))&gt; (Int))
-&gt; i:(Int)
-&gt; ((Vec &lt;True, \k10 VV -&gt; ((VV == 0) || (VV == (fib k10)))&gt; (Int)), {VV : (Int) | (VV == (fib i))})</span><span class='hs-definition'>fibMemo</span></a> <a class=annot href="#"><span class=annottext>(Vec &lt;True, \k10 VV -&gt; ((VV == 0) || (VV == (fib k10)))&gt; (Int))</span><span class='hs-varid'>t</span></a> <a class=annot href="#"><span class=annottext>(Int)</span><span class='hs-varid'>i</span></a> 
<span class=hs-linenum>354: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == i)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:(Int)
-&gt; x2:(Int) -&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 &lt;= x2))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a>    
<span class=hs-linenum>355: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a-&gt; b-&gt; Bool&gt;.
x1:a
-&gt; x2:{VV : b&lt;p2 x1&gt; | true}
-&gt; {x3 : (a, b)&lt;p2&gt; | ((fst x3) == x1) &amp;&amp; ((snd x3) == x2)}</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{x2 : (Vec &lt;True, \x7 VV -&gt; ((x6 == 0) || (x6 == (fib x7)))&gt; (Int)) | (x2 == t)}</span><span class='hs-varid'>t</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>x1:(Bool)
-&gt; {x8 : (Int) | (x8 == 1) &amp;&amp; (x8 &gt; 0) &amp;&amp; (x8 &gt;= i)}
-&gt; {x8 : (Int) | ((Prop x1)) &amp;&amp; (x8 == 1) &amp;&amp; (x8 &gt; 0) &amp;&amp; (x8 &gt;= i)}</span><span class='hs-varid'>liquidAssume</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:(Int)
-&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; ((fib x1) == (if (x1 &lt;= 1) then 1 else ((fib (x1 - 1)) + (fib (x1 - 2))))))}</span><span class='hs-varid'>axiom_fib</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == i)}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>356: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> 
<span class=hs-linenum>357: </span>  <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>case</span> <a class=annot href="#"><span class=annottext>forall &lt;r :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool, d :: (GHC.Types.Int)-&gt; Bool&gt;.
x1:{x7 : (Int)&lt;d&gt; | true}
-&gt; (Vec &lt;d, \x5 VV -&gt; r x5&gt; (Int)) -&gt; {x6 : (Int)&lt;r x1&gt; | true}</span><span class='hs-varid'>get</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == i)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Vec &lt;True, \x7 VV -&gt; ((x6 == 0) || (x6 == (fib x7)))&gt; (Int)) | (x2 == t)}</span><span class='hs-varid'>t</span></a> <span class='hs-keyword'>of</span>   
<span class=hs-linenum>358: </span>     <span class='hs-num'>0</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>let</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Vec &lt;True, \x1 VV -&gt; ((VV == 0) || (VV == (fib x1)))&gt; (Int)) | (VV == t1)}</span><span class='hs-varid'>t1</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV == n1)}</span><span class='hs-varid'>n1</span></a><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(Vec &lt;True, \x18 VV -&gt; ((x17 == 0) || (x17 == (fib x18)))&gt; (Int))
-&gt; x2:(Int)
-&gt; ((Vec &lt;True, \x8 VV -&gt; ((x7 == 0) || (x7 == (fib x8)))&gt; (Int)), {x11 : (Int) | (x11 == (fib x2))})</span><span class='hs-varid'>fibMemo</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Vec &lt;True, \x7 VV -&gt; ((x6 == 0) || (x6 == (fib x7)))&gt; (Int)) | (x2 == t)}</span><span class='hs-varid'>t</span></a>  <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == i)}</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 - x2))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>359: </span>              <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Vec &lt;(VV /= i), \x1 VV -&gt; ((VV == 0) || (VV == (fib x1)))&gt; (Int)) | (VV == t2)}</span><span class='hs-varid'>t2</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV == n2)}</span><span class='hs-varid'>n2</span></a><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(Vec &lt;True, \x18 VV -&gt; ((x17 == 0) || (x17 == (fib x18)))&gt; (Int))
-&gt; x2:(Int)
-&gt; ((Vec &lt;True, \x8 VV -&gt; ((x7 == 0) || (x7 == (fib x8)))&gt; (Int)), {x11 : (Int) | (x11 == (fib x2))})</span><span class='hs-varid'>fibMemo</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Vec &lt;True, \x8 VV -&gt; ((x7 == 0) || (x7 == (fib x8)))&gt; (Int)) | (x3 == t1) &amp;&amp; (x3 == t1)}</span><span class='hs-varid'>t1</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == i)}</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 - x2))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (2  :  int))}</span><span class='hs-num'>2</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>360: </span>              <a class=annot href="#"><span class=annottext>(Int)</span><span class='hs-varid'>n</span></a>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(Bool) -&gt; (Int) -&gt; {x2 : (Int) | ((Prop x1))}</span><span class='hs-varid'>liquidAssume</span></a> 
<span class=hs-linenum>361: </span>                        <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:(Int)
-&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; ((fib x1) == (if (x1 &lt;= 1) then 1 else ((fib (x1 - 1)) + (fib (x1 - 2))))))}</span><span class='hs-varid'>axiom_fib</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == i)}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == n1) &amp;&amp; (x3 == n1)}</span><span class='hs-varid'>n1</span></a><a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a><a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == n2) &amp;&amp; (x3 == n2)}</span><span class='hs-varid'>n2</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>362: </span>          <span class='hs-keyword'>in</span> <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a-&gt; b-&gt; Bool&gt;.
x1:a
-&gt; x2:{VV : b&lt;p2 x1&gt; | true}
-&gt; {x3 : (a, b)&lt;p2&gt; | ((fst x3) == x1) &amp;&amp; ((snd x3) == x2)}</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>forall &lt;r :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool, d :: (GHC.Types.Int)-&gt; Bool&gt;.
x1:{x13 : (Int)&lt;d&gt; | true}
-&gt; {x12 : (Int)&lt;r x1&gt; | true}
-&gt; (Vec &lt;d &amp; (x8 /= x1), \x10 VV -&gt; r x10&gt; (Int))
-&gt; (Vec &lt;d, \x4 VV -&gt; r x4&gt; (Int))</span><span class='hs-varid'>set</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == i)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == n)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Vec &lt;(x5 /= i), \x9 VV -&gt; ((x8 == 0) || (x8 == (fib x9)))&gt; (Int)) | (x3 == t2) &amp;&amp; (x3 == t2)}</span><span class='hs-varid'>t2</span></a><span class='hs-layout'>,</span>  <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == n)}</span><span class='hs-varid'>n</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>363: </span>     <span class='hs-varid'>n</span> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{x2 : ({x7 : (Vec &lt;True, \x12 VV -&gt; ((x11 == 0) || (x11 == (fib x12)))&gt; (Int)) | (x7 == t)}, {x16 : (Int) | (x16 == (fib i)) &amp;&amp; (x16 /= 0)})&lt;\_ VV -&gt; (x16 == (fib i)) &amp;&amp; (x16 /= 0)&gt; | ((fst x2) == t)}</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{x2 : (Vec &lt;True, \x7 VV -&gt; ((x6 == 0) || (x6 == (fib x7)))&gt; (Int)) | (x2 == t)}</span><span class='hs-varid'>t</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{x3 : (Int) | ((x3 == 0) || (x3 == (fib i)))}</span><span class='hs-varid'>n</span></a><span class='hs-layout'>)</span>
</pre>

Memoized Fibonacci 
------------------

- `fibMemo` *takes* a table initialized with `0`
- `fibMemo` *returns* a table with `fib` values upto `n`.

<br>


<pre><span class=hs-linenum>375: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fibMemo</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>FibV</span> 
<span class=hs-linenum>376: </span>            <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> 
<span class=hs-linenum>377: </span>            <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>FibV</span><span class='hs-layout'>,</span><span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = (fib i)}</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>


Recap
-----

Created a `Vec` container 

Decoupled *domain* and *range* invariants from *data*

<br>

<div class="fragment">

Previous, special purpose program analyses 

- [Gopan-Reps-Sagiv, POPL 05](link)
- [J.-McMillan, CAV 07](link)
- [Logozzo-Cousot-Cousot, POPL 11](link)
- [Dillig-Dillig, POPL 12](link) 
- ...

Encoded as instance of abstract refinement types!
</div>




