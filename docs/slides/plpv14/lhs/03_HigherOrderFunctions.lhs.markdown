  {#hofs}
=========

<div class="hidden">

<pre><span class=hs-linenum> 6: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Loop</span> <span class='hs-layout'>(</span>
<span class=hs-linenum> 7: </span>    <span class='hs-varid'>listSum</span>
<span class=hs-linenum> 8: </span>  <span class='hs-layout'>,</span> <span class='hs-varid'>listNatSum</span>
<span class=hs-linenum> 9: </span>  <span class='hs-layout'>)</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>10: </span>
<span class=hs-linenum>11: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span>
<span class=hs-linenum>12: </span>
<span class=hs-linenum>13: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-termination"</span><span class='hs-keyword'>@-}</span>
<span class=hs-linenum>14: </span><span class='hs-definition'>listNatSum</span>  <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>15: </span><span class='hs-definition'>add</span>         <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
</pre>
</div>

Higher-Order Specifications
---------------------------

Types scale to *Higher-Order* Specifications

<br>

<div class="fragment">

+ map
+ fold
+ visitors
+ callbacks
+ ...

</div>

<br>

<div class="fragment">Very difficult with *first-order program logics*</div>


Higher Order Specifications
===========================

Example: Higher Order Loop
--------------------------


<pre><span class=hs-linenum>48: </span><span class='hs-definition'>loop</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span>
<span class=hs-linenum>49: </span><a class=annot href="#"><span class=annottext>forall a.
lo:{VV : (Int) | (VV == 0) &amp;&amp; (VV &gt;= 0)}
-&gt; hi:{VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &gt;= lo)}
-&gt; a
-&gt; ({VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &gt;= lo) &amp;&amp; (VV &lt; hi)} -&gt; a -&gt; a)
-&gt; a</span><span class='hs-definition'>loop</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV == 0) &amp;&amp; (VV &gt;= 0)}</span><span class='hs-varid'>lo</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &gt;= lo)}</span><span class='hs-varid'>hi</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>base</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &gt;= lo) &amp;&amp; (VV &lt; hi)} -&gt; a -&gt; a</span><span class='hs-varid'>f</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x4 : (Int) | (x4 &gt;= 0) &amp;&amp; (x4 &gt;= lo) &amp;&amp; (x4 &lt;= hi)} -&gt; a -&gt; a</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{x4 : (Int) | (x4 == 0) &amp;&amp; (x4 == lo) &amp;&amp; (x4 &gt;= 0)}</span><span class='hs-varid'>lo</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == base)}</span><span class='hs-varid'>base</span></a>
<span class=hs-linenum>50: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>51: </span>    <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &gt;= lo) &amp;&amp; (VV &lt;= hi)} -&gt; a -&gt; a</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &gt;= lo) &amp;&amp; (VV &lt;= hi)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>acc</span></a> 
<span class=hs-linenum>52: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == i) &amp;&amp; (x5 &gt;= 0) &amp;&amp; (x5 &gt;= lo) &amp;&amp; (x5 &lt;= hi)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:{x12 : (Int) | (x12 &gt;= 0) &amp;&amp; (x12 &gt;= i) &amp;&amp; (x12 &gt;= lo) &amp;&amp; (x12 &lt;= hi)}
-&gt; x2:{x12 : (Int) | (x12 &gt;= 0) &amp;&amp; (x12 &gt;= i) &amp;&amp; (x12 &gt;= lo) &amp;&amp; (x12 &lt;= hi)}
-&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{x4 : (Int) | (x4 == hi) &amp;&amp; (x4 &gt;= 0) &amp;&amp; (x4 &gt;= lo)}</span><span class='hs-varid'>hi</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &gt;= lo) &amp;&amp; (VV &lt;= hi)} -&gt; a -&gt; a</span><span class='hs-varid'>go</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == i) &amp;&amp; (x5 &gt;= 0) &amp;&amp; (x5 &gt;= lo) &amp;&amp; (x5 &lt;= hi)}</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x4 : (Int) | (x4 &gt;= 0) &amp;&amp; (x4 &gt;= lo) &amp;&amp; (x4 &lt; hi)} -&gt; a -&gt; a</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{x5 : (Int) | (x5 == i) &amp;&amp; (x5 &gt;= 0) &amp;&amp; (x5 &gt;= lo) &amp;&amp; (x5 &lt;= hi)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == acc)}</span><span class='hs-varid'>acc</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>53: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == acc)}</span><span class='hs-varid'>acc</span></a>
</pre>

<br>

LiquidHaskell infers `f` called with values `(Btwn lo hi)`


Example: Summing Lists
----------------------


<pre><span class=hs-linenum>65: </span><a class=annot href="#"><span class=annottext>forall a. (Num a) =&gt; [a] -&gt; a</span><span class='hs-definition'>listSum</span></a> <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>xs</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x12 : (Int) | (x12 == 0) &amp;&amp; (x12 &gt;= 0)}
-&gt; x2:{x9 : (Int) | (x9 &gt;= 0) &amp;&amp; (x9 &gt;= x1)}
-&gt; a
-&gt; ({x6 : (Int) | (x6 &gt;= 0) &amp;&amp; (x6 &gt;= x1) &amp;&amp; (x6 &lt; x2)} -&gt; a -&gt; a)
-&gt; a</span><span class='hs-varid'>loop</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == n) &amp;&amp; (x3 == (len xs))}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 &gt;= 0) &amp;&amp; (x3 &lt; n)} -&gt; a -&gt; a</span><span class='hs-varid'>body</span></a> 
<span class=hs-linenum>66: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>67: </span>    <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; n)} -&gt; a -&gt; a</span><span class='hs-varid'>body</span></a>    <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>\</span><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; n)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>acc</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == acc)}</span><span class='hs-varid'>acc</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; x2:a -&gt; {VV : a | (VV == (x1 + x2))}</span><span class='hs-varop'>+</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x4 : [a] | (x4 == xs) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>x1:[a] -&gt; {x3 : (Int) | (x3 &lt; (len x1)) &amp;&amp; (0 &lt;= x3)} -&gt; a</span><span class='hs-varop'>!!</span></a> <a class=annot href="#"><span class=annottext>{x4 : (Int) | (x4 == i) &amp;&amp; (x4 &gt;= 0) &amp;&amp; (x4 &lt; n)}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>68: </span>    <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (len xs))}</span><span class='hs-varid'>n</span></a>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:[a] -&gt; {x2 : (Int) | (x2 == (len x1))}</span><span class='hs-varid'>length</span></a> <a class=annot href="#"><span class=annottext>{x4 : [a] | (x4 == xs) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

<br>

- <div class="fragment">*Function subtyping:* `body` called on `i :: Btwn 0 (llen xs)`</div>
- <div class="fragment">Hence, indexing with `!!` is safe.</div>


<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=Loop.hs" target= "_blank">Demo:</a> Tweak `loop` exit condition? 
</div>

Example: Summing `Nat`s
-----------------------

<br>


<pre><span class=hs-linenum>87: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>listNatSum</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Nat</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Nat</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>88: </span><a class=annot href="#"><span class=annottext>[{VV : (Int) | (VV &gt;= 0)}] -&gt; {VV : (Int) | (VV &gt;= 0)}</span><span class='hs-definition'>listNatSum</span></a> <a class=annot href="#"><span class=annottext>[{VV : (Int) | (VV &gt;= 0)}]</span><span class='hs-varid'>xs</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x20 : (Int) | (x20 == 0) &amp;&amp; (x20 &gt;= 0)}
-&gt; x2:{x17 : (Int) | (x17 &gt;= 0) &amp;&amp; (x17 &gt;= x1)}
-&gt; {x14 : (Int) | (x14 &gt;= 0)}
-&gt; ({x12 : (Int) | (x12 &gt;= 0) &amp;&amp; (x12 &gt;= x1) &amp;&amp; (x12 &lt; x2)}
    -&gt; {x14 : (Int) | (x14 &gt;= 0)} -&gt; {x14 : (Int) | (x14 &gt;= 0)})
-&gt; {x14 : (Int) | (x14 &gt;= 0)}</span><span class='hs-varid'>loop</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == n) &amp;&amp; (x3 == (len xs))}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>{x8 : (Int) | (x8 &gt;= 0) &amp;&amp; (x8 &lt; n)}
-&gt; x2:{x5 : (Int) | (x5 &gt;= 0)}
-&gt; {x3 : (Int) | (x3 &gt;= 0) &amp;&amp; (x3 &gt;= x2)}</span><span class='hs-varid'>body</span></a> 
<span class=hs-linenum>89: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>90: </span>    <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; n)}
-&gt; acc:{VV : (Int) | (VV &gt;= 0)}
-&gt; {VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &gt;= acc)}</span><span class='hs-varid'>body</span></a>       <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>\</span><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &lt; n)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0)}</span><span class='hs-varid'>acc</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == acc) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>acc</span></a> <a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{x4 : [{x7 : (Int) | (x7 &gt;= 0)}] | (x4 == xs) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>x1:[{x9 : (Int) | (x9 &gt;= 0)}]
-&gt; {x5 : (Int) | (x5 &lt; (len x1)) &amp;&amp; (0 &lt;= x5)}
-&gt; {x9 : (Int) | (x9 &gt;= 0)}</span><span class='hs-varop'>!!</span></a> <a class=annot href="#"><span class=annottext>{x4 : (Int) | (x4 == i) &amp;&amp; (x4 &gt;= 0) &amp;&amp; (x4 &lt; n)}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>91: </span>    <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (len xs))}</span><span class='hs-varid'>n</span></a>          <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:[{x6 : (Int) | (x6 &gt;= 0)}] -&gt; {x2 : (Int) | (x2 == (len x1))}</span><span class='hs-varid'>length</span></a> <a class=annot href="#"><span class=annottext>{x4 : [{x7 : (Int) | (x7 &gt;= 0)}] | (x4 == xs) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

<br>

<div class="fragment" align="center">

----  ----  ---------------------------------------
 (+)  `::`  `x:Int -> y:Int -> {v:Int| v=x+y}`
      `<:`  `Nat   -> Nat   -> Nat`
----  ----  ---------------------------------------

</div>

Example: Summing `Nat`s
-----------------------

 <br> 
<pre><span class=hs-linenum>109: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>listNatSum</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Nat</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Nat</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>110: </span><span class='hs-definition'>listNatSum</span> <span class='hs-varid'>xs</span>  <span class='hs-keyglyph'>=</span> <span class='hs-varid'>loop</span> <span class='hs-num'>0</span> <span class='hs-varid'>n</span> <span class='hs-num'>0</span> <span class='hs-varid'>body</span> 
<span class=hs-linenum>111: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>112: </span>    <span class='hs-varid'>body</span>       <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>\</span><span class='hs-varid'>i</span> <span class='hs-varid'>acc</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>acc</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>xs</span> <span class='hs-varop'>!!</span> <span class='hs-varid'>i</span><span class='hs-layout'>)</span>
<span class=hs-linenum>113: </span>    <span class='hs-varid'>n</span>          <span class='hs-keyglyph'>=</span> <span class='hs-varid'>length</span> <span class='hs-varid'>xs</span>
</pre>

<br>

Hence, verified by *instantiating* `α` of `loop` with `Nat`

<div class="fragment">`Int -> Int -> Nat -> (Int -> Nat -> Nat) -> Nat`</div>

Example: Summing `Nat`s
-----------------------

 <br> 
<pre><span class=hs-linenum>126: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>listNatSum</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Nat</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Nat</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>127: </span><span class='hs-definition'>listNatSum</span> <span class='hs-varid'>xs</span>  <span class='hs-keyglyph'>=</span> <span class='hs-varid'>loop</span> <span class='hs-num'>0</span> <span class='hs-varid'>n</span> <span class='hs-num'>0</span> <span class='hs-varid'>body</span> 
<span class=hs-linenum>128: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>129: </span>    <span class='hs-varid'>body</span>       <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>\</span><span class='hs-varid'>i</span> <span class='hs-varid'>acc</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>acc</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>xs</span> <span class='hs-varop'>!!</span> <span class='hs-varid'>i</span><span class='hs-layout'>)</span>
<span class=hs-linenum>130: </span>    <span class='hs-varid'>n</span>          <span class='hs-keyglyph'>=</span> <span class='hs-varid'>length</span> <span class='hs-varid'>xs</span>
</pre>

<br>

+ Parameter `α` corresponds to *loop invariant*

+ Instantiation corresponds to invariant *synthesis*


Instantiation And Inference
---------------------------

+ <div class="fragment">Polymorphic instantiation happens *everywhere*</div> 

+ <div class="fragment">Automatic inference is crucial</div>

+ <div class="fragment">*Cannot use* unification (unlike indexed approaches)</div>

+ <div class="fragment">*Can reuse* [SMT/predicate abstraction.](http://goto.ucsd.edu/~rjhala/papers/liquid_types.html)</div>



Iteration Dependence
--------------------

**Cannot** use parametric polymorphism to verify:

<br>


<pre><span class=hs-linenum>161: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>add</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>m</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Nat</span><span class='hs-keyword'>|v=m+n}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>162: </span><a class=annot href="#"><span class=annottext>n:{VV : (Int) | (VV &gt;= 0)}
-&gt; m:{VV : (Int) | (VV &gt;= 0)}
-&gt; {VV : (Int) | (VV == (m + n)) &amp;&amp; (VV &gt;= 0)}</span><span class='hs-definition'>add</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0)}</span><span class='hs-varid'>m</span></a> <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>x1:{x24 : (Int) | (x24 == 0) &amp;&amp; (x24 &gt;= 0)}
-&gt; x2:{x21 : (Int) | (x21 &gt;= 0) &amp;&amp; (x21 &gt;= x1)}
-&gt; {x18 : (Int) | (x18 &gt;= 0) &amp;&amp; (x18 &gt;= n)}
-&gt; ({x15 : (Int) | (x15 &gt;= 0) &amp;&amp; (x15 &gt;= x1) &amp;&amp; (x15 &lt; x2)}
    -&gt; {x18 : (Int) | (x18 &gt;= 0) &amp;&amp; (x18 &gt;= n)}
    -&gt; {x18 : (Int) | (x18 &gt;= 0) &amp;&amp; (x18 &gt;= n)})
-&gt; {x18 : (Int) | (x18 &gt;= 0) &amp;&amp; (x18 &gt;= n)}</span><span class='hs-varid'>loop</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (0  :  int))}</span><span class='hs-num'>0</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == m) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>m</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{x3 : (Int) | (x3 == n) &amp;&amp; (x3 &gt;= 0)}</span><span class='hs-varid'>n</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-layout'>(</span></span><span class=hs-error><a class=annot href="#"><span class=annottext>{x11 : (Int) | (x11 &gt;= 0) &amp;&amp; (x11 &lt; m)}
-&gt; x2:{x8 : (Int) | (x8 &gt;= 0) &amp;&amp; (x8 &gt;= n)}
-&gt; {x5 : (Int) | (x5 &gt; 0) &amp;&amp; (x5 &gt; x2) &amp;&amp; (x5 &gt; n) &amp;&amp; (x5 &gt;= 0)}</span><span class='hs-keyglyph'>\</span></a></span><span class=hs-error><span class='hs-keyword'>_</span></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt;= 0) &amp;&amp; (VV &gt;= n)}</span><span class='hs-varid'>i</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-keyglyph'>-&gt;</span></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{x4 : (Int) | (x4 == i) &amp;&amp; (x4 &gt;= 0) &amp;&amp; (x4 &gt;= n)}</span><span class='hs-varid'>i</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a></span><span class=hs-error><span class='hs-layout'>)</span></span>
</pre>

<br>


- <div class="fragment">As property only holds after **last** loop iteration...</div>

- <div class="fragment">... cannot instantiate `α` with `{v:Int | v = n + m}`</div>

<div class="fragment">**Problem:** Need *iteration-dependent* invariants...</div>

