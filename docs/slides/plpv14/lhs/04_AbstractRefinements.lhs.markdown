  {#abstractrefinements}
========================

<div class="hidden">


<pre><span class=hs-linenum>7: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>AbstractRefinements</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>8: </span>
<span class=hs-linenum>9: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span> 
<span class=hs-linenum>10: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span>
<span class=hs-linenum>11: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-termination"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>12: </span>
<span class=hs-linenum>13: </span><span class='hs-definition'>o</span><span class='hs-layout'>,</span> <span class='hs-varid'>no</span>        <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>14: </span><span class='hs-definition'>maxInt</span>       <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
</pre>
</div>



Abstract Refinements
--------------------



Abstract Refinements
====================

Two Problems
------------

<div class="fragment">

**Problem 1:** 

How do we specify *both* [increasing and decreasing lists](http://web.cecs.pdx.edu/~sheard/Code/QSort.html)?

</div>

<br>

<div class="fragment">

**Problem 2:** 

How do we specify *iteration-dependence* in higher-order functions?

</div>


Problem Is Pervasive
--------------------

Lets distill it to a simple example...

<div class="fragment">

<br>

(First, a few aliases)

<br>


<pre><span class=hs-linenum>64: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>Odd</span>  <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>v</span> <span class='hs-varid'>mod</span> <span class='hs-num'>2</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>65: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>Even</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>v</span> <span class='hs-varid'>mod</span> <span class='hs-num'>2</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

</div>


Example: `maxInt` 
-----------------

Compute the larger of two `Int`s:

 <br> 
<pre><span class=hs-linenum>77: </span><span class='hs-definition'>maxInt</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> 
<span class=hs-linenum>78: </span><span class='hs-definition'>maxInt</span> <span class='hs-varid'>x</span> <span class='hs-varid'>y</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>if</span> <span class='hs-varid'>y</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>x</span> <span class='hs-keyword'>then</span> <span class='hs-varid'>x</span> <span class='hs-keyword'>else</span> <span class='hs-varid'>y</span>
</pre>



Example: `maxInt` 
-----------------

Has *many incomparable* refinement types

<br>
<pre><span class=hs-linenum>89: </span><span class='hs-definition'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Nat</span>  <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Nat</span>  <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Nat</span>
<span class=hs-linenum>90: </span><span class='hs-definition'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Even</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Even</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Even</span>
<span class=hs-linenum>91: </span><span class='hs-definition'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Odd</span>  <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Odd</span>  <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Odd</span> 
</pre>

<br>

<div class="fragment">Yikes. **Which** one should we use?</div>


Refinement Polymorphism 
-----------------------

`maxInt` returns *one of* its two inputs `x` and `y` 

<div align="center">

<br>

---------   ---   -------------------------------------------
   **If**    :    the *inputs* satisfy a property  

 **Then**    :    the *output* satisfies that property
---------   ---   -------------------------------------------

<br>

</div>

<div class="fragment">Above holds *for all* properties!</div>

<br>

<div class="fragment"> 

**Need to abstract refinements over types**

</div>


By Type Polymorphism?
---------------------

 <br> 
<pre><span class=hs-linenum>133: </span><span class='hs-definition'>max</span>     <span class='hs-keyglyph'>::</span> <span class='hs-varid'>α</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span> 
<span class=hs-linenum>134: </span><span class='hs-definition'>max</span> <span class='hs-varid'>x</span> <span class='hs-varid'>y</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>if</span> <span class='hs-varid'>y</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>x</span> <span class='hs-keyword'>then</span> <span class='hs-varid'>x</span> <span class='hs-keyword'>else</span> <span class='hs-varid'>y</span>
</pre>

<div class="fragment"> 

Instantiate `α` at callsites


<pre><span class=hs-linenum>142: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>o</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Odd</span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>143: </span><a class=annot href="#"><span class=annottext>{VV : (Int) | ((VV mod 2) == 1)}</span><span class='hs-definition'>o</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; Bool&gt;.
{x3 : (Int)&lt;p&gt; | true}
-&gt; {x2 : (Int)&lt;p&gt; | true} -&gt; {x1 : (Int)&lt;p&gt; | true}</span><span class='hs-varid'>maxInt</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (3  :  int))}</span><span class='hs-num'>3</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (7  :  int))}</span><span class='hs-num'>7</span></a>     <span class='hs-comment'>-- α := Odd</span>
<span class=hs-linenum>144: </span>
<span class=hs-linenum>145: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>e</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Even</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>146: </span><a class=annot href="#"><span class=annottext>{VV : (Int) | ((VV mod 2) == 0)}</span><span class='hs-definition'>e</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; Bool&gt;.
{x3 : (Int)&lt;p&gt; | true}
-&gt; {x2 : (Int)&lt;p&gt; | true} -&gt; {x1 : (Int)&lt;p&gt; | true}</span><span class='hs-varid'>maxInt</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (2  :  int))}</span><span class='hs-num'>2</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (8  :  int))}</span><span class='hs-num'>8</span></a>     <span class='hs-comment'>-- α := Even</span>
</pre>

</div>

By Type Polymorphism?
---------------------

 <br> 
<pre><span class=hs-linenum>155: </span><span class='hs-definition'>max</span>     <span class='hs-keyglyph'>::</span> <span class='hs-varid'>α</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span> 
<span class=hs-linenum>156: </span><span class='hs-definition'>max</span> <span class='hs-varid'>x</span> <span class='hs-varid'>y</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>if</span> <span class='hs-varid'>y</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>x</span> <span class='hs-keyword'>then</span> <span class='hs-varid'>x</span> <span class='hs-keyword'>else</span> <span class='hs-varid'>y</span>
</pre>

<br>

But there is a fly in the ointment ...

Polymorphic `max` in Haskell
----------------------------

 In Haskell the type of max is
<pre><span class=hs-linenum>167: </span><span class='hs-definition'>max</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>α</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>α</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span>
</pre>

<br>

 Could *ignore* the class constraints, instantiate as before...
<pre><span class=hs-linenum>173: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>o</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Odd</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>174: </span><span class='hs-definition'>o</span>     <span class='hs-keyglyph'>=</span> <span class='hs-varid'>max</span> <span class='hs-num'>3</span> <span class='hs-num'>7</span>  <span class='hs-comment'>-- α := Odd </span>
</pre>


Polymorphic `(+)` in Haskell
----------------------------

 ... but this is *unsound*!
<pre><span class=hs-linenum>182: </span><span class='hs-definition'>max</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>α</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>α</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span>
<span class=hs-linenum>183: </span><span class='hs-layout'>(</span><span class='hs-varop'>+</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Num</span> <span class='hs-varid'>α</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>α</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>α</span>
</pre>

<br>

<div class="fragment">

*Ignoring* class constraints would let us "prove":


<pre><span class=hs-linenum>193: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>no</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Odd</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>194: </span><a class=annot href="#"><span class=annottext>{VV : (Int) | ((VV mod 2) == 1)}</span><span class='hs-definition'>no</span></a>     <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (3  :  int))}</span><span class='hs-num'>3</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>x1:(Int) -&gt; x2:(Int) -&gt; {x4 : (Int) | (x4 == (x1 + x2))}</span><span class='hs-varop'>+</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (7  :  int))}</span><span class='hs-num'>7</span></a></span>    <span class='hs-comment'>-- α := Odd !</span>
</pre>

</div>

Type Polymorphism? No.
----------------------

<div class="fragment">Need to try a bit harder...</div>

By Parametric Refinements!
--------------------------

That is, enable *quantification over refinements*...

Parametric Refinements 
----------------------


<pre><span class=hs-linenum>213: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> 
<span class=hs-linenum>214: </span>                <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>215: </span>
<span class=hs-linenum>216: </span><a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; Bool&gt;.
{VV : (Int)&lt;p&gt; | true}
-&gt; {VV : (Int)&lt;p&gt; | true} -&gt; {VV : (Int)&lt;p&gt; | true}</span><span class='hs-definition'>maxInt</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((papp1 p VV))}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((papp1 p VV))}</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>if</span> <a class=annot href="#"><span class=annottext>{x3 : (Int) | ((papp1 p x3)) &amp;&amp; (x3 == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:{x6 : (Int) | ((papp1 p x6))}
-&gt; x2:{x6 : (Int) | ((papp1 p x6))}
-&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 &lt;= x2))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Int) | ((papp1 p x3)) &amp;&amp; (x3 == y)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyword'>then</span> <a class=annot href="#"><span class=annottext>{x3 : (Int) | ((papp1 p x3)) &amp;&amp; (x3 == y)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyword'>else</span> <a class=annot href="#"><span class=annottext>{x3 : (Int) | ((papp1 p x3)) &amp;&amp; (x3 == x)}</span><span class='hs-varid'>x</span></a> 
</pre>

<br>


<div class="fragment">Type says: **for any** `p` that is a property of `Int`, </div>

- <div class="fragment">`max` **takes** two `Int`s that satisfy `p`,</div>

- <div class="fragment">`max` **returns** an `Int` that satisfies `p`.</div>

Parametric Refinements 
----------------------

<br>
<pre><span class=hs-linenum>232: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> 
<span class=hs-linenum>233: </span>                <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>234: </span>
<span class=hs-linenum>235: </span><span class='hs-definition'>maxInt</span> <span class='hs-varid'>x</span> <span class='hs-varid'>y</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>if</span> <span class='hs-varid'>x</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>y</span> <span class='hs-keyword'>then</span> <span class='hs-varid'>y</span> <span class='hs-keyword'>else</span> <span class='hs-varid'>x</span> 
</pre>

<br>

[Key idea: ](http://goto.ucsd.edu/~rjhala/papers/abstract_refinement_types.html) `Int<p>` is `{v:Int | (p v)}`

<br>

<div class="fragment">So, Abstract Refinement is an *uninterpreted function* in SMT logic</div>

Parametric Refinements 
----------------------

<br>
<pre><span class=hs-linenum>250: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> 
<span class=hs-linenum>251: </span>                <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>252: </span>
<span class=hs-linenum>253: </span><span class='hs-definition'>maxInt</span> <span class='hs-varid'>x</span> <span class='hs-varid'>y</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>if</span> <span class='hs-varid'>x</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>y</span> <span class='hs-keyword'>then</span> <span class='hs-varid'>y</span> <span class='hs-keyword'>else</span> <span class='hs-varid'>x</span> 
</pre>

<br>

**Check** and **Instantiate** type using *SMT & predicate abstraction*

Using Abstract Refinements
--------------------------

- <div class="fragment">**When** we call `maxInt` with args with some refinement,</div>

- <div class="fragment">**Then** `p` instantiated with *same* refinement,</div>

- <div class="fragment">**Result** of call will also have concrete refinement.</div>

<div class="fragment">


<pre><span class=hs-linenum>272: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>o'</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Odd</span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>273: </span><a class=annot href="#"><span class=annottext>{VV : (Int) | ((VV mod 2) == 1)}</span><span class='hs-definition'>o'</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; Bool&gt;.
{x3 : (Int)&lt;p&gt; | true}
-&gt; {x2 : (Int)&lt;p&gt; | true} -&gt; {x1 : (Int)&lt;p&gt; | true}</span><span class='hs-varid'>maxInt</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (3  :  int))}</span><span class='hs-num'>3</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (7  :  int))}</span><span class='hs-num'>7</span></a>     <span class='hs-comment'>-- p := \v -&gt; Odd v </span>
<span class=hs-linenum>274: </span>
<span class=hs-linenum>275: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>e'</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Even</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>276: </span><a class=annot href="#"><span class=annottext>{VV : (Int) | ((VV mod 2) == 0)}</span><span class='hs-definition'>e'</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; Bool&gt;.
{x3 : (Int)&lt;p&gt; | true}
-&gt; {x2 : (Int)&lt;p&gt; | true} -&gt; {x1 : (Int)&lt;p&gt; | true}</span><span class='hs-varid'>maxInt</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (2  :  int))}</span><span class='hs-num'>2</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (8  :  int))}</span><span class='hs-num'>8</span></a>     <span class='hs-comment'>-- p := \v -&gt; Even v </span>
</pre>

</div>

Using Abstract Refinements
--------------------------

Or any other property 

<br>


<pre><span class=hs-linenum>289: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>RGB</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-num'>0</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&lt;</span> <span class='hs-num'>256</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>290: </span>
<span class=hs-linenum>291: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>rgb</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>RGB</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>292: </span><a class=annot href="#"><span class=annottext>{v : (Int) | (v &lt; 256) &amp;&amp; (0 &lt;= v)}</span><span class='hs-definition'>rgb</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; Bool&gt;.
{x3 : (Int)&lt;p&gt; | true}
-&gt; {x2 : (Int)&lt;p&gt; | true} -&gt; {x1 : (Int)&lt;p&gt; | true}</span><span class='hs-varid'>maxInt</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (56  :  int))}</span><span class='hs-num'>56</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (8  :  int))}</span><span class='hs-num'>8</span></a>
</pre>


Recap
-----

1. **Refinements:** Types + Predicates
2. **Subtyping:** SMT Implication
3. **Measures:** Strengthened Constructors
4. <div class="fragment">**Abstract:** Refinements over Type Signatures</div>

