Abstract Refinements {#composition}
===================================

Very General Mechanism 
----------------------

**Next:** Lets add parameters...

<div class="hidden">

<pre><span class=hs-linenum>11: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Composition</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>12: </span>
<span class=hs-linenum>13: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varop'>.</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>14: </span>
<span class=hs-linenum>15: </span><span class='hs-definition'>plus</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>16: </span><span class='hs-definition'>plus3'</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
</pre>
</div>


Example: `plus`
---------------


<pre><span class=hs-linenum>25: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>plus</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyword'>_</span> <span class='hs-keyword'>| v=x+y}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>26: </span><a class=annot href="#"><span class=annottext>x:(Int) -&gt; y:(Int) -&gt; {v : (Int) | (v == (x + y))}</span><span class='hs-definition'>plus</span></a> <a class=annot href="#"><span class=annottext>(Int)</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>(Int)</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == y)}</span><span class='hs-varid'>y</span></a>
</pre>


Example: `plus 3` 
-----------------

<br>


<pre><span class=hs-linenum>36: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>plus3'</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = x + 3}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>37: </span><a class=annot href="#"><span class=annottext>x:(Int) -&gt; {VV : (Int) | (VV == (x + 3))}</span><span class='hs-definition'>plus3'</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x2 : (Int) | (x2 == (x1 + x2))}</span><span class='hs-varid'>plus</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (3  :  int))}</span><span class='hs-num'>3</span></a>
</pre>

<br>

Easily verified by LiquidHaskell

A Composed Variant
------------------

Lets define `plus3` by *composition*

A Composition Operator 
----------------------


<pre><span class=hs-linenum>53: </span><span class='hs-layout'>(</span><span class='hs-cpp'>#</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>c</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>c</span>
<span class=hs-linenum>54: </span><a class=annot href="#"><span class=annottext>forall a b c. (a -&gt; b) -&gt; (c -&gt; a) -&gt; c -&gt; b</span><span class='hs-layout'>(</span></a><span class='hs-cpp'>#</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>g</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>f</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>a -&gt; b</span><span class='hs-varid'>g</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span>
</pre>


`plus3` By Composition
-----------------------


<pre><span class=hs-linenum>62: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>plus3''</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = x + 3}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>63: </span><a class=annot href="#"><span class=annottext>x:(Int) -&gt; {VV : (Int) | (VV == (x + 3))}</span><span class='hs-definition'>plus3''</span></a>     <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x2 : (Int) | (x2 == (x1 + x2))}</span><span class='hs-varid'>plus</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>((Int) -&gt; (Int)) -&gt; ((Int) -&gt; (Int)) -&gt; (Int) -&gt; (Int)</span><span class='hs-cpp'>#</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x2 : (Int) | (x2 == (x1 + x2))}</span><span class='hs-varid'>plus</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (2  :  int))}</span><span class='hs-num'>2</span></a></span>
</pre>

<br>

Yikes! Verification *fails*. But why?

<br>

<div class="fragment">(Hover mouse over `#` for a clue)</div>

How to type compose (#) ? 
-------------------------

This specification is *too weak* <br>

 <br>
<pre><span class=hs-linenum>80: </span><span class='hs-layout'>(</span><span class='hs-cpp'>#</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>c</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>c</span><span class='hs-layout'>)</span>
</pre>

<br>

Output type does not *relate* `c` with `a`!

How to type compose (.) ?
-------------------------

Write specification with abstract refinement type:

<br>


<pre><span class=hs-linenum>95: </span><span class='hs-keyword'>{-@</span> <span class='hs-layout'>(</span><span class='hs-varop'>.</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>b</span><span class='hs-keyglyph'>-&gt;</span><span class='hs-varid'>c</span><span class='hs-keyglyph'>-&gt;</span><span class='hs-conid'>Prop</span><span class='hs-layout'>,</span> 
<span class=hs-linenum>96: </span>                   <span class='hs-varid'>q</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-keyglyph'>-&gt;</span><span class='hs-varid'>b</span><span class='hs-keyglyph'>-&gt;</span><span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span>
<span class=hs-linenum>97: </span>             <span class='hs-varid'>f</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>c</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>x</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>98: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>g</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>q</span> <span class='hs-varid'>x</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>99: </span>          <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>exists</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>z</span><span class='hs-conop'>:</span><span class='hs-varid'>b</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>q</span> <span class='hs-varid'>y</span><span class='hs-varop'>&gt;</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>.</span><span class='hs-varid'>c</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>z</span><span class='hs-varop'>&gt;</span>
<span class=hs-linenum>100: </span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>101: </span><a class=annot href="#"><span class=annottext>forall a b c &lt;p :: b-&gt; a-&gt; Bool, q :: c-&gt; b-&gt; Bool&gt;.
(x:b -&gt; {VV : a&lt;p x&gt; | true})
-&gt; (x:c -&gt; {VV : b&lt;q x&gt; | true})
-&gt; y:c
-&gt; exists [z:{VV : b&lt;q y&gt; | true}].{VV : a&lt;p z&gt; | true}</span><span class='hs-layout'>(</span></a><span class='hs-varop'>.</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x:a -&gt; {VV : b | ((papp2 p VV x))}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; {VV : b | ((papp2 q VV x))}</span><span class='hs-varid'>g</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:a -&gt; {VV : b | ((papp2 p VV x1))}</span><span class='hs-varid'>f</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:a -&gt; {VV : b | ((papp2 q VV x1))}</span><span class='hs-varid'>g</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a><span class='hs-layout'>)</span>
</pre>

Using (.) Operator 
------------------

<br>


<pre><span class=hs-linenum>110: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>plus3</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = x + 3}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>111: </span><a class=annot href="#"><span class=annottext>x:(Int) -&gt; {VV : (Int) | (VV == (x + 3))}</span><span class='hs-definition'>plus3</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x2 : (Int) | (x2 == (x1 + x2))}</span><span class='hs-varid'>plus</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a> <a class=annot href="#"><span class=annottext>forall &lt;q :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool, p :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool&gt;.
(x:(Int) -&gt; {x8 : (Int)&lt;p x&gt; | true})
-&gt; (x:(Int) -&gt; {x9 : (Int)&lt;q x&gt; | true})
-&gt; x3:(Int)
-&gt; exists [z:{x9 : (Int)&lt;q x3&gt; | true}].{x8 : (Int)&lt;p z&gt; | true}</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x2 : (Int) | (x2 == (x1 + x2))}</span><span class='hs-varid'>plus</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (2  :  int))}</span><span class='hs-num'>2</span></a>
</pre>

<br>

<div class="fragment">*Verifies!*</div>


Using (.) Operator 
------------------

 <br>
<pre><span class=hs-linenum>123: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>plus3</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = x + 3}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>124: </span><span class='hs-definition'>plus3</span>     <span class='hs-keyglyph'>=</span> <span class='hs-varid'>plus</span> <span class='hs-num'>1</span> <span class='hs-varop'>.</span> <span class='hs-varid'>plus</span> <span class='hs-num'>2</span>
</pre>

<br>

LiquidHaskell *instantiates*

- `p` with `\x -> v = x + 1`
- `q` with `\x -> v = x + 2`

Using (.) Operator 
------------------

 <br>
<pre><span class=hs-linenum>138: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>plus3</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = x + 3}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>139: </span><span class='hs-definition'>plus3</span>     <span class='hs-keyglyph'>=</span> <span class='hs-varid'>plus</span> <span class='hs-num'>1</span> <span class='hs-varop'>.</span> <span class='hs-varid'>plus</span> <span class='hs-num'>2</span>
</pre>

<br> To *infer* that output of `plus3` has type: 

`exists [z:{v = y + 2}].{v = z + 1}`

<div class="fragment">

`<:`

`{v:Int|v=3}`
</div>


Recap
-----

1. **Refinements:** Types + Predicates
2. **Subtyping:** SMT Implication
3. **Measures:** Strengthened Constructors
4. **Abstract:** Refinements over Type Signatures
    + <div class="fragment">*Dependencies* using refinement parameters</div>
