Decouple Invariants From Data {#recursive} 
==========================================

Recursive Structures 
--------------------

<div class="fragment">
Lets see another example of decoupling...
</div>

<div class="hidden">

<pre><span class=hs-linenum>13: </span><span class='hs-comment'>{-# LANGUAGE NoMonomorphismRestriction #-}</span>
<span class=hs-linenum>14: </span>
<span class=hs-linenum>15: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>List</span> <span class='hs-layout'>(</span><span class='hs-varid'>insertSort</span><span class='hs-layout'>)</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>16: </span>
<span class=hs-linenum>17: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-termination"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>18: </span>
<span class=hs-linenum>19: </span><span class='hs-definition'>mergeSort</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>20: </span><span class='hs-definition'>insertSort</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>21: </span><span class='hs-definition'>slist</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>22: </span><span class='hs-definition'>slist'</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>23: </span><span class='hs-definition'>iGoUp</span><span class='hs-layout'>,</span> <span class='hs-varid'>iGoDn</span><span class='hs-layout'>,</span> <span class='hs-varid'>iDiff</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>24: </span><span class='hs-keyword'>infixr</span> <span class='hs-varop'>`C`</span>
</pre>
</div>

Decouple Invariants From Recursive Data
=======================================

Recall: Lists
-------------


<pre><span class=hs-linenum>35: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span> 
<span class=hs-linenum>36: </span>         <span class='hs-keyglyph'>|</span> <span class='hs-conid'>C</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
</pre>


Recall: Refined Constructors 
----------------------------

Define *increasing* Lists with strengthened constructors:

 <br>
<pre><span class=hs-linenum>46: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>47: </span>  <span class='hs-conid'>N</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>48: </span>  <span class='hs-conid'>C</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>hd</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>tl</span><span class='hs-conop'>:</span> <span class='hs-conid'>L</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>hd</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span>
</pre>

Problem: Decreasing Lists?
--------------------------

What if we need *both* [increasing and decreasing lists](http://web.cecs.pdx.edu/~sheard/Code/QSort.html)?

<br>

<div class="fragment">
*Separate* types are tedious...
</div>


Abstract That Refinement!
-------------------------


<pre><span class=hs-linenum>67: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>L</span> <span class='hs-varid'>a</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;</span>
<span class=hs-linenum>68: </span>      <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span> 
<span class=hs-linenum>69: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-conid'>C</span> <span class='hs-layout'>(</span><span class='hs-varid'>hd</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>tl</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>L</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>hd</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>

<br>

- <div class="fragment"> `p` is a *binary* relation between two `a` values</div>

- <div class="fragment"> Definition relates `hd` with *all* the elements of `tl`</div>

- <div class="fragment"> Recursive: `p` holds for *every pair* of elements!</div>

Example
-------

Consider a list with *three* or more elements 

 <br>
<pre><span class=hs-linenum>86: </span><span class='hs-definition'>x1</span> <span class='hs-varop'>`C`</span> <span class='hs-varid'>x2</span> <span class='hs-varop'>`C`</span> <span class='hs-varid'>x3</span> <span class='hs-varop'>`C`</span> <span class='hs-varid'>rest</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>a</span> 
</pre>

Example: Unfold Once
--------------------

 <br> 
<pre><span class=hs-linenum>93: </span><span class='hs-definition'>x1</span>                 <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>94: </span><span class='hs-definition'>x2</span> <span class='hs-varop'>`C`</span> <span class='hs-varid'>x3</span> <span class='hs-varop'>`C`</span> <span class='hs-varid'>rest</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>x1</span><span class='hs-varop'>&gt;</span> 
</pre>

Example: Unfold Twice
---------------------

 <br> 
<pre><span class=hs-linenum>101: </span><span class='hs-definition'>x1</span>          <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>102: </span><span class='hs-definition'>x2</span>          <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>x1</span><span class='hs-varop'>&gt;</span>  
<span class=hs-linenum>103: </span><span class='hs-definition'>x3</span> <span class='hs-varop'>`C`</span> <span class='hs-varid'>rest</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>x1</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>p</span> <span class='hs-varid'>x2</span><span class='hs-varop'>&gt;</span> 
</pre>

Example: Unfold Thrice
----------------------

 <br> 
<pre><span class=hs-linenum>110: </span><span class='hs-definition'>x1</span>   <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>111: </span><span class='hs-definition'>x2</span>   <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>x1</span><span class='hs-varop'>&gt;</span>  
<span class=hs-linenum>112: </span><span class='hs-definition'>x3</span>   <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>x1</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>p</span> <span class='hs-varid'>x2</span><span class='hs-varop'>&gt;</span>  
<span class=hs-linenum>113: </span><span class='hs-definition'>rest</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>L</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>x1</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>p</span> <span class='hs-varid'>x2</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-varid'>p</span> <span class='hs-varid'>x3</span><span class='hs-varop'>&gt;</span> 
</pre>

<br>

<div class="fragment">
Note how `p` holds between **every pair** of elements in the list. 
</div>

A Concrete Example
------------------

That was a rather *abstract*!

<br>

How can we *use* fact that `p` holds between *every pair* ?


Example: Increasing Lists
-------------------------

*Instantiate* `p` with a *concrete* refinement

<br>


<pre><span class=hs-linenum>140: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>IncL</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>L</span> <span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>hd</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>hd</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
</pre>

<br>

- <div class="fragment"> Refinement says `hd` less than each tail element `v`,</div>

- <div class="fragment"> Thus, `IncL` denotes *increaing* lists. </div>

Example: Increasing Lists
-------------------------

LiquidHaskell verifies that `slist` is indeed increasing...


<pre><span class=hs-linenum>155: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>slist</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>IncL</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>156: </span><a class=annot href="#"><span class=annottext>(L &lt;\hd2 VV -&gt; (hd2 &lt;= VV)&gt; (Int))</span><span class='hs-definition'>slist</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool&gt;.
x1:{x10 : (Int) | (x10 &gt; 0)}
-&gt; (L &lt;p&gt; {x10 : (Int)&lt;p x1&gt; | (x10 &gt; 0)})
-&gt; (L &lt;p&gt; {x10 : (Int) | (x10 &gt; 0)})</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (6  :  int))}</span><span class='hs-num'>6</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool&gt;.
x1:{x10 : (Int) | (x10 &gt; 0)}
-&gt; (L &lt;p&gt; {x10 : (Int)&lt;p x1&gt; | (x10 &gt; 0)})
-&gt; (L &lt;p&gt; {x10 : (Int) | (x10 &gt; 0)})</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (12  :  int))}</span><span class='hs-num'>12</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool&gt;.
x1:{x10 : (Int) | (x10 &gt; 0)}
-&gt; (L &lt;p&gt; {x10 : (Int)&lt;p x1&gt; | (x10 &gt; 0)})
-&gt; (L &lt;p&gt; {x10 : (Int) | (x10 &gt; 0)})</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>(L &lt;\_ VV -&gt; false&gt; {x3 : (Int) | false})</span><span class='hs-conid'>N</span></a>
</pre>

<br> 

<div class="fragment">

... and protests that `slist'` is not: 


<pre><span class=hs-linenum>166: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>slist'</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>IncL</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>167: </span><a class=annot href="#"><span class=annottext>(L &lt;\hd2 VV -&gt; (hd2 &lt;= VV)&gt; (Int))</span><span class='hs-definition'>slist'</span></a> <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (6  :  int))}</span><span class='hs-num'>6</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool&gt;.
x1:{x10 : (Int) | (x10 &gt; 0)}
-&gt; (L &lt;p&gt; {x10 : (Int)&lt;p x1&gt; | (x10 &gt; 0)})
-&gt; (L &lt;p&gt; {x10 : (Int) | (x10 &gt; 0)})</span><span class='hs-varop'>`C`</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool&gt;.
x1:{x10 : (Int) | (x10 &gt; 0)}
-&gt; (L &lt;p&gt; {x10 : (Int)&lt;p x1&gt; | (x10 &gt; 0)})
-&gt; (L &lt;p&gt; {x10 : (Int) | (x10 &gt; 0)})</span><span class='hs-varop'>`C`</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (12  :  int))}</span><span class='hs-num'>12</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>forall &lt;p :: (GHC.Types.Int)-&gt; (GHC.Types.Int)-&gt; Bool&gt;.
x1:{x10 : (Int) | (x10 &gt; 0)}
-&gt; (L &lt;p&gt; {x10 : (Int)&lt;p x1&gt; | (x10 &gt; 0)})
-&gt; (L &lt;p&gt; {x10 : (Int) | (x10 &gt; 0)})</span><span class='hs-varop'>`C`</span></a></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>(L &lt;\_ VV -&gt; false&gt; {x3 : (Int) | false})</span><span class='hs-conid'>N</span></a></span>
</pre>
</div>

Insertion Sort
--------------


<pre><span class=hs-linenum>175: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>insertSort</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>IncL</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>176: </span><a class=annot href="#"><span class=annottext>forall a. (Ord a) =&gt; [a] -&gt; (L &lt;\hd2 VV -&gt; (hd2 &lt;= VV)&gt; a)</span><span class='hs-definition'>insertSort</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(a
 -&gt; (L &lt;\x11 VV -&gt; (VV &gt;= x11)&gt; a)
 -&gt; (L &lt;\x11 VV -&gt; (VV &gt;= x11)&gt; a))
-&gt; (L &lt;\x11 VV -&gt; (VV &gt;= x11)&gt; a)
-&gt; [a]
-&gt; (L &lt;\x11 VV -&gt; (VV &gt;= x11)&gt; a)</span><span class='hs-varid'>foldr</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (L &lt;\x4 VV -&gt; (VV &gt;= x4)&gt; a) -&gt; (L &lt;\x2 VV -&gt; (VV &gt;= x2)&gt; a)</span><span class='hs-varid'>insert</span></a> <a class=annot href="#"><span class=annottext>(L &lt;\_ VV -&gt; false&gt; {VV : a | false})</span><span class='hs-conid'>N</span></a>
<span class=hs-linenum>177: </span>
<span class=hs-linenum>178: </span><a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
a -&gt; (L &lt;\x2 VV -&gt; (VV &gt;= x2)&gt; a) -&gt; (L &lt;\x1 VV -&gt; (VV &gt;= x1)&gt; a)</span><span class='hs-definition'>insert</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>y</span></a> <span class='hs-conid'>N</span>          <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:{VV : a | (VV == y)}
-&gt; (L &lt;p&gt; {VV : a&lt;p x1&gt; | (VV == y)})
-&gt; (L &lt;p&gt; {VV : a | (VV == y)})</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>(L &lt;\_ VV -&gt; false&gt; {VV : a | false})</span><span class='hs-conid'>N</span></a>
<span class=hs-linenum>179: </span><span class='hs-definition'>insert</span> <span class='hs-varid'>y</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-varop'>`C`</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>180: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; x2:a -&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a>           <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:{VV : a | (VV &gt;= y)}
-&gt; (L &lt;p&gt; {VV : a&lt;p x1&gt; | (VV &gt;= y)})
-&gt; (L &lt;p&gt; {VV : a | (VV &gt;= y)})</span><span class='hs-varop'>`C`</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:{VV : a | (VV &gt; y) &amp;&amp; (VV &gt;= x)}
-&gt; (L &lt;p&gt; {VV : a&lt;p x1&gt; | (VV &gt; y) &amp;&amp; (VV &gt;= x)})
-&gt; (L &lt;p&gt; {VV : a | (VV &gt; y) &amp;&amp; (VV &gt;= x)})</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>{x2 : (L &lt;\x3 VV -&gt; (VV &gt;= x3)&gt; {VV : a | (VV &gt;= x)}) | (x2 == xs)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>181: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:{VV : a | (VV &gt;= x)}
-&gt; (L &lt;p&gt; {VV : a&lt;p x1&gt; | (VV &gt;= x)})
-&gt; (L &lt;p&gt; {VV : a | (VV &gt;= x)})</span><span class='hs-varop'>`C`</span></a> <a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
a -&gt; (L &lt;\x2 VV -&gt; (VV &gt;= x2)&gt; a) -&gt; (L &lt;\x1 VV -&gt; (VV &gt;= x1)&gt; a)</span><span class='hs-varid'>insert</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>{x2 : (L &lt;\x3 VV -&gt; (VV &gt;= x3)&gt; {VV : a | (VV &gt;= x)}) | (x2 == xs)}</span><span class='hs-varid'>xs</span></a>
</pre>

<br>

(*Hover* over `insert'` to see inferred type.)

Checking GHC Lists
------------------

<a href="http://goto.ucsd.edu:8090/index.html#?demo=Order.hs" target= "_blank">Demo:</a> 
Above applies to GHC's List definition:

 <br> 
<pre><span class=hs-linenum>195: </span><span class='hs-keyword'>data</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;</span>
<span class=hs-linenum>196: </span>  <span class='hs-keyglyph'>=</span> <span class='hs-conid'>[]</span> 
<span class=hs-linenum>197: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conop'>:</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>h</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>tl</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>h</span><span class='hs-varop'>&gt;</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
</pre>

Checking GHC Lists
------------------

Increasing Lists

<br>


<pre><span class=hs-linenum>208: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>Incs</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>h</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>h</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>209: </span>
<span class=hs-linenum>210: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>iGoUp</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Incs</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>211: </span><a class=annot href="#"><span class=annottext>[(Int)]&lt;\h6 VV -&gt; (h6 &lt;= VV)&gt;</span><span class='hs-definition'>iGoUp</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x4 : [{x14 : (Int) | (x14 &gt; 0)}]&lt;\x11 VV -&gt; (x11 /= x12) &amp;&amp; (x12 &gt; 0) &amp;&amp; (x12 &gt; x11) &amp;&amp; (x11 &lt;= x12)&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (2  :  int))}</span><span class='hs-num'>2</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (3  :  int))}</span><span class='hs-num'>3</span></a><span class='hs-keyglyph'>]</span>
</pre>

Checking GHC Lists
------------------

Decreasing Lists

<br>


<pre><span class=hs-linenum>222: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>Decs</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>h</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>h</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>223: </span>
<span class=hs-linenum>224: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>iGoDn</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Decs</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>225: </span><a class=annot href="#"><span class=annottext>[(Int)]&lt;\h8 VV -&gt; (h8 &gt;= VV)&gt;</span><span class='hs-definition'>iGoDn</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x4 : [{x15 : (Int) | (x15 &gt; 0)}]&lt;\x13 VV -&gt; (x12 == 1) &amp;&amp; (x13 /= x12) &amp;&amp; (x12 &gt; 0) &amp;&amp; (x13 &gt;= x12) &amp;&amp; (x12 &lt; x13)&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (3  :  int))}</span><span class='hs-num'>3</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (2  :  int))}</span><span class='hs-num'>2</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-keyglyph'>]</span>
</pre>


Checking GHC Lists
------------------

Duplicate-free Lists

<br>


<pre><span class=hs-linenum>237: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>Difs</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>h</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>h</span> <span class='hs-varop'>/=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>238: </span>
<span class=hs-linenum>239: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>iDiff</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Difs</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>240: </span><a class=annot href="#"><span class=annottext>[(Int)]&lt;\h10 VV -&gt; (h10 /= VV)&gt;</span><span class='hs-definition'>iDiff</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x4 : [{x14 : (Int) | (x14 &gt; 0)}]&lt;\x12 VV -&gt; (x12 /= x11) &amp;&amp; (x11 &gt; 0) &amp;&amp; (x12 &gt;= x11) &amp;&amp; (x11 &lt; x12)&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (3  :  int))}</span><span class='hs-num'>3</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{x2 : (Int) | (x2 == (2  :  int))}</span><span class='hs-num'>2</span></a><span class='hs-keyglyph'>]</span>
</pre>

Checking GHC Lists
------------------

Now we can check all the usual list sorting algorithms 

Example: `mergeSort` [1/2]
--------------------------


<pre><span class=hs-linenum>252: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>mergeSort</span>  <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Incs</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>253: </span><a class=annot href="#"><span class=annottext>forall a. (Ord a) =&gt; [a] -&gt; [a]&lt;\h6 VV -&gt; (h6 &lt;= VV)&gt;</span><span class='hs-definition'>mergeSort</span></a> <span class='hs-conid'>[]</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
{x4 : [{VV : a | false}]&lt;p&gt; | (((null x4)) &lt;=&gt; true) &amp;&amp; ((len x4) == 0) &amp;&amp; ((sumLens x4) == 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>254: </span><span class='hs-definition'>mergeSort</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x6 : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (((null x6)) &lt;=&gt; true) &amp;&amp; ((len x6) == 0) &amp;&amp; ((sumLens x6) == 0) &amp;&amp; ((len x6) &gt;= 0) &amp;&amp; ((sumLens x6) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>255: </span><span class='hs-definition'>mergeSort</span> <span class='hs-varid'>xs</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x10 : [a]&lt;\x11 VV -&gt; (VV &gt;= x11)&gt; | ((len x10) &gt;= 0)}
-&gt; x2:{x7 : [a]&lt;\x8 VV -&gt; (VV &gt;= x8)&gt; | ((len x7) &gt;= 0)}
-&gt; {x4 : [a]&lt;\x5 VV -&gt; (x5 &lt;= VV)&gt; | ((len x4) &gt;= 0) &amp;&amp; ((len x4) &gt;= (len x1)) &amp;&amp; ((len x4) &gt;= (len x2))}</span><span class='hs-varid'>merge</span></a> <a class=annot href="#"><span class=annottext>{x4 : [a]&lt;\x5 VV -&gt; (x5 &lt;= VV)&gt; | (x4 == xs1') &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>xs1'</span></a> <a class=annot href="#"><span class=annottext>{x4 : [a]&lt;\x5 VV -&gt; (x5 &lt;= VV)&gt; | (x4 == xs2') &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>xs2'</span></a> 
<span class=hs-linenum>256: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>257: </span>   <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs1) &amp;&amp; ((len VV) == (len xs1)) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &gt;= (len xs2))}</span><span class='hs-varid'>xs1</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs2) &amp;&amp; ((len VV) == (len xs2)) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len xs1)) &amp;&amp; ((len VV) &lt;= (len xs1))}</span><span class='hs-varid'>xs2</span></a><span class='hs-layout'>)</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x14 : [a] | ((len x14) &gt; 0)}
-&gt; ({x9 : [a] | ((len x9) &gt;= 0) &amp;&amp; ((len x9) &lt;= (len x1))}, {x12 : [a] | ((len x12) &gt;= 0) &amp;&amp; ((len x12) &lt;= (len x1))})&lt;\x5 VV -&gt; ((len x6) &gt;= 0) &amp;&amp; ((len x6) &lt;= (len x5)) &amp;&amp; ((len x6) &lt;= (len x1))&gt;</span><span class='hs-varid'>split</span></a> <a class=annot href="#"><span class=annottext>{x3 : [a] | ((len x3) &gt;= 0) &amp;&amp; ((sumLens x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>258: </span>   <a class=annot href="#"><span class=annottext>[a]&lt;\x2 VV -&gt; (x2 &lt;= VV)&gt;</span><span class='hs-varid'>xs1'</span></a>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[a] -&gt; [a]&lt;\x2 VV -&gt; (x2 &lt;= VV)&gt;</span><span class='hs-varid'>mergeSort</span></a> <a class=annot href="#"><span class=annottext>{x7 : [a] | (x7 == xs1) &amp;&amp; (x7 == xs1) &amp;&amp; ((len x7) == (len xs1)) &amp;&amp; ((len x7) &gt;= 0) &amp;&amp; ((len x7) &gt;= (len xs2)) &amp;&amp; ((sumLens x7) &gt;= 0)}</span><span class='hs-varid'>xs1</span></a>
<span class=hs-linenum>259: </span>   <a class=annot href="#"><span class=annottext>[a]&lt;\x2 VV -&gt; (x2 &lt;= VV)&gt;</span><span class='hs-varid'>xs2'</span></a>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[a] -&gt; [a]&lt;\x2 VV -&gt; (x2 &lt;= VV)&gt;</span><span class='hs-varid'>mergeSort</span></a> <a class=annot href="#"><span class=annottext>{x8 : [a] | (x8 == xs2) &amp;&amp; (x8 == xs2) &amp;&amp; ((len x8) == (len xs2)) &amp;&amp; ((len x8) &gt;= 0) &amp;&amp; ((sumLens x8) &gt;= 0) &amp;&amp; ((len x8) &lt;= (len xs1)) &amp;&amp; ((len x8) &lt;= (len xs1))}</span><span class='hs-varid'>xs2</span></a>
</pre>

Example: `mergeSort` [1/2]
--------------------------


<pre><span class=hs-linenum>266: </span><a class=annot href="#"><span class=annottext>forall a.
x1:{VV : [a] | ((len VV) &gt;= 0)}
-&gt; ({VV : [a] | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))}, {VV : [a] | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))})&lt;\x1 VV -&gt; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1)) &amp;&amp; ((len VV) &lt;= (len x1))&gt;</span><span class='hs-definition'>split</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>zs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a-&gt; b-&gt; Bool&gt;.
x1:a
-&gt; x2:{VV : b&lt;p2 x1&gt; | true}
-&gt; {x3 : (a, b)&lt;p2&gt; | ((fst x3) == x1) &amp;&amp; ((snd x3) == x2)}</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:a
-&gt; x2:[{VV : a&lt;p x1&gt; | true}]&lt;p&gt;
-&gt; {x4 : [a]&lt;p&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) == (1 + (len x2))) &amp;&amp; ((sumLens x4) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{x8 : [a] | (x8 == xs) &amp;&amp; (x8 == xs) &amp;&amp; ((len x8) == (len xs)) &amp;&amp; ((len x8) &gt;= 0) &amp;&amp; ((len x8) &gt;= (len ys)) &amp;&amp; ((sumLens x8) &gt;= 0) &amp;&amp; ((len x8) &lt;= (len zs))}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:a
-&gt; x2:[{VV : a&lt;p x1&gt; | true}]&lt;p&gt;
-&gt; {x4 : [a]&lt;p&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) == (1 + (len x2))) &amp;&amp; ((sumLens x4) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{x9 : [a] | (x9 == ys) &amp;&amp; (x9 == ys) &amp;&amp; ((len x9) == (len ys)) &amp;&amp; ((len x9) &gt;= 0) &amp;&amp; ((sumLens x9) &gt;= 0) &amp;&amp; ((len x9) &lt;= (len xs)) &amp;&amp; ((len x9) &lt;= (len xs)) &amp;&amp; ((len x9) &lt;= (len zs))}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span> 
<span class=hs-linenum>267: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>268: </span>    <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; ((len VV) == (len xs)) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &gt;= (len ys)) &amp;&amp; ((len VV) &lt;= (len zs))}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == ys) &amp;&amp; ((len VV) == (len ys)) &amp;&amp; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len xs)) &amp;&amp; ((len VV) &lt;= (len xs)) &amp;&amp; ((len VV) &lt;= (len zs))}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
x1:{VV : [a] | ((len VV) &gt;= 0)}
-&gt; ({VV : [a] | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))}, {VV : [a] | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))})&lt;\x1 VV -&gt; ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1)) &amp;&amp; ((len VV) &lt;= (len x1))&gt;</span><span class='hs-varid'>split</span></a> <a class=annot href="#"><span class=annottext>{x4 : [a] | (x4 == zs) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>zs</span></a>
<span class=hs-linenum>269: </span><span class='hs-definition'>split</span> <span class='hs-varid'>xs</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a-&gt; b-&gt; Bool&gt;.
x1:a
-&gt; x2:{VV : b&lt;p2 x1&gt; | true}
-&gt; {x3 : (a, b)&lt;p2&gt; | ((fst x3) == x1) &amp;&amp; ((snd x3) == x2)}</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{x3 : [a] | ((len x3) &gt;= 0) &amp;&amp; ((sumLens x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{x6 : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (((null x6)) &lt;=&gt; true) &amp;&amp; ((len x6) == 0) &amp;&amp; ((sumLens x6) == 0) &amp;&amp; ((len x6) &gt;= 0) &amp;&amp; ((sumLens x6) &gt;= 0)}</span><span class='hs-conid'>[]</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>270: </span>
<span class=hs-linenum>271: </span><a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
xs:{VV : [a]&lt;\x3 VV -&gt; (VV &gt;= x3)&gt; | ((len VV) &gt;= 0)}
-&gt; x1:{VV : [a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt; | ((len VV) &gt;= 0)}
-&gt; {VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &gt;= (len x1)) &amp;&amp; ((len VV) &gt;= (len xs))}</span><span class='hs-definition'>merge</span></a> <a class=annot href="#"><span class=annottext>{VV : [a]&lt;\x1 VV -&gt; (VV &gt;= x1)&gt; | ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <span class='hs-conid'>[]</span>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x4 : [a]&lt;\x5 VV -&gt; (VV &gt;= x5)&gt; | (x4 == xs) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>272: </span><span class='hs-definition'>merge</span> <span class='hs-conid'>[]</span> <span class='hs-varid'>ys</span>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x3 : [a]&lt;\x4 VV -&gt; (VV &gt;= x4)&gt; | ((len x3) &gt;= 0) &amp;&amp; ((sumLens x3) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
<span class=hs-linenum>273: </span><span class='hs-definition'>merge</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>ys</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>274: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; x2:a -&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 &lt;= x2))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:{VV : a | (x &lt;= VV)}
-&gt; x2:[{VV : a&lt;p x1&gt; | (x &lt;= VV)}]&lt;p&gt;
-&gt; {x4 : [{VV : a | (x &lt;= VV)}]&lt;p&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) == (1 + (len x2))) &amp;&amp; ((sumLens x4) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
xs:{VV : [a]&lt;\x3 VV -&gt; (VV &gt;= x3)&gt; | ((len VV) &gt;= 0)}
-&gt; x1:{VV : [a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt; | ((len VV) &gt;= 0)}
-&gt; {VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &gt;= (len x1)) &amp;&amp; ((len VV) &gt;= (len xs))}</span><span class='hs-varid'>merge</span></a> <a class=annot href="#"><span class=annottext>{x4 : [{VV : a | (VV &gt;= x)}]&lt;\x5 VV -&gt; (VV &gt;= x5)&gt; | (x4 == xs) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:{VV : a | (x &lt;= VV) &amp;&amp; (y &lt;= VV)}
-&gt; x2:[{VV : a&lt;p x1&gt; | (x &lt;= VV) &amp;&amp; (y &lt;= VV)}]&lt;p&gt;
-&gt; {x4 : [{VV : a | (x &lt;= VV) &amp;&amp; (y &lt;= VV)}]&lt;p&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) == (1 + (len x2))) &amp;&amp; ((sumLens x4) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{x4 : [{VV : a | (VV &gt;= y)}]&lt;\x5 VV -&gt; (VV &gt;= x5)&gt; | (x4 == ys) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>275: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:{VV : a | (VV &gt;= y)}
-&gt; x2:[{VV : a&lt;p x1&gt; | (VV &gt;= y)}]&lt;p&gt;
-&gt; {x4 : [{VV : a | (VV &gt;= y)}]&lt;p&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) == (1 + (len x2))) &amp;&amp; ((sumLens x4) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
xs:{VV : [a]&lt;\x3 VV -&gt; (VV &gt;= x3)&gt; | ((len VV) &gt;= 0)}
-&gt; x1:{VV : [a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt; | ((len VV) &gt;= 0)}
-&gt; {VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &gt;= (len x1)) &amp;&amp; ((len VV) &gt;= (len xs))}</span><span class='hs-varid'>merge</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:{VV : a | (VV &gt; y)}
-&gt; x2:[{VV : a&lt;p x1&gt; | (VV &gt; y)}]&lt;p&gt;
-&gt; {x4 : [{VV : a | (VV &gt; y)}]&lt;p&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) == (1 + (len x2))) &amp;&amp; ((sumLens x4) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{x4 : [{VV : a | (VV &gt;= x)}]&lt;\x5 VV -&gt; (VV &gt;= x5)&gt; | (x4 == xs) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x4 : [{VV : a | (VV &gt;= y)}]&lt;\x5 VV -&gt; (VV &gt;= x5)&gt; | (x4 == ys) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
</pre>

Example: `Data.List.sort` 
-------------------------

GHC's "official" list sorting routine

Juggling lists of increasing & decreasing lists


Ex: `Data.List.sort` [1/4]
--------------------------

Juggling lists of increasing & decreasing lists

<br>


<pre><span class=hs-linenum>294: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>sort</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Incs</span> <span class='hs-varid'>a</span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>295: </span><a class=annot href="#"><span class=annottext>forall a. (Ord a) =&gt; [a] -&gt; [a]&lt;\h6 VV -&gt; (h6 &lt;= VV)&gt;</span><span class='hs-definition'>sort</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x5 : [{x9 : [a]&lt;\x10 VV -&gt; (x10 &lt;= VV)&gt; | ((len x9) &gt;= 0)}]&lt;\_ VV -&gt; ((len x7) &gt;= 0)&gt; | ((len x5) &gt; 0)}
-&gt; {x2 : [a]&lt;\x3 VV -&gt; (x3 &lt;= VV)&gt; | ((len x2) &gt;= 0)}</span><span class='hs-varid'>mergeAll</span></a> <a class=annot href="#"><span class=annottext>forall &lt;q :: [a]-&gt; [[a]]-&gt; Bool, p :: [[a]]-&gt; [a]-&gt; Bool&gt;.
(x:{x26 : [{x30 : [a]&lt;\x31 VV -&gt; (x31 &lt;= VV)&gt; | ((len x30) &gt;= 0)}]&lt;\_ VV -&gt; ((len x28) &gt;= 0)&gt; | ((len x26) &gt; 0)}
 -&gt; {x23 : [a]&lt;\x24 VV -&gt; (x24 &lt;= VV)&gt;&lt;p x&gt; | ((len x23) &gt;= 0)})
-&gt; (y:[a]
    -&gt; {x26 : [{x30 : [a]&lt;\x31 VV -&gt; (x31 &lt;= VV)&gt; | ((len x30) &gt;= 0)}]&lt;\_ VV -&gt; ((len x28) &gt;= 0)&gt;&lt;q y&gt; | ((len x26) &gt; 0)})
-&gt; x3:[a]
-&gt; exists [z:{x26 : [{x30 : [a]&lt;\x31 VV -&gt; (x31 &lt;= VV)&gt; | ((len x30) &gt;= 0)}]&lt;\_ VV -&gt; ((len x28) &gt;= 0)&gt;&lt;q x3&gt; | ((len x26) &gt; 0)}].{x23 : [a]&lt;\x24 VV -&gt; (x24 &lt;= VV)&gt;&lt;p z&gt; | ((len x23) &gt;= 0)}</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>[a]
-&gt; {x2 : [{x6 : [a]&lt;\x7 VV -&gt; (x7 &lt;= VV)&gt; | ((len x6) &gt;= 0)}]&lt;\_ VV -&gt; ((len x4) &gt;= 0)&gt; | ((len x2) &gt; 0)}</span><span class='hs-varid'>sequences</span></a>
<span class=hs-linenum>296: </span>
<span class=hs-linenum>297: </span><a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
[a]
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-definition'>sequences</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>a</span><span class='hs-conop'>:</span><span class='hs-varid'>b</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>298: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x1:a
-&gt; x2:a
-&gt; {x4 : (Ordering) | ((x4 == GHC.Types.EQ) &lt;=&gt; (x1 == x2)) &amp;&amp; ((x4 == GHC.Types.GT) &lt;=&gt; (x1 &gt; x2)) &amp;&amp; ((x4 == GHC.Types.LT) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>`compare`</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>x1:(Ordering)
-&gt; x2:(Ordering) -&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 == x2))}</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Ordering) | (x3 == GHC.Types.GT) &amp;&amp; ((cmp x3) == GHC.Types.GT)}</span><span class='hs-conid'>GT</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
a:a
-&gt; {VV : [{VV : a | (VV &gt; a)}]&lt;\x2 VV -&gt; (VV &gt; a) &amp;&amp; (VV &gt; x2)&gt; | ((len VV) &gt; 0)}
-&gt; {VV : [a] | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>descending</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>{x4 : [{VV : a | (VV == a) &amp;&amp; (VV &gt; b)}]&lt;\_ VV -&gt; false&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a><span class='hs-keyglyph'>]</span>  <a class=annot href="#"><span class=annottext>{x4 : [a] | (x4 == xs) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>299: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>           <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
a:a
-&gt; (x1:{VV : [{VV : a | (VV &gt;= a)}]&lt;\x3 VV -&gt; (a &lt;= VV) &amp;&amp; (x3 &lt;= VV)&gt; | ((len VV) &gt; 0)}
    -&gt; {VV : [a]&lt;\x2 VV -&gt; (x2 &lt;= VV)&gt; | (VV /= x1) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len x1))})
-&gt; {VV : [a] | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>ascending</span></a>  <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:{VV : a | (a &lt;= VV)}
-&gt; x2:[{VV : a&lt;p x1&gt; | (a &lt;= VV)}]&lt;p&gt;
-&gt; {x4 : [{VV : a | (a &lt;= VV)}]&lt;p&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) == (1 + (len x2))) &amp;&amp; ((sumLens x4) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x4 : [a] | (x4 == xs) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>300: </span><span class='hs-definition'>sequences</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span>           <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x6 : [{x8 : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | false}]&lt;\_ VV -&gt; false&gt; | (((null x6)) &lt;=&gt; true) &amp;&amp; ((len x6) == 0) &amp;&amp; ((sumLens x6) == 0) &amp;&amp; ((len x6) &gt;= 0) &amp;&amp; ((sumLens x6) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{x4 : [{VV : a | (VV == a)}]&lt;\_ VV -&gt; false&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>301: </span><span class='hs-definition'>sequences</span> <span class='hs-conid'>[]</span>            <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x6 : [{x8 : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | false}]&lt;\_ VV -&gt; false&gt; | (((null x6)) &lt;=&gt; true) &amp;&amp; ((len x6) == 0) &amp;&amp; ((sumLens x6) == 0) &amp;&amp; ((len x6) &gt;= 0) &amp;&amp; ((sumLens x6) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{x6 : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | (((null x6)) &lt;=&gt; true) &amp;&amp; ((len x6) == 0) &amp;&amp; ((sumLens x6) == 0) &amp;&amp; ((len x6) &gt;= 0) &amp;&amp; ((sumLens x6) &gt;= 0)}</span><span class='hs-conid'>[]</span></a><span class='hs-keyglyph'>]</span>
</pre>

Ex: `Data.List.sort` [2/4]
--------------------------

Juggling lists of increasing & decreasing lists

<br>


<pre><span class=hs-linenum>312: </span><a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
a:a
-&gt; {VV : [{VV : a | (VV &gt; a)}]&lt;\x2 VV -&gt; (VV &gt; a) &amp;&amp; (VV &gt; x2)&gt; | ((len VV) &gt; 0)}
-&gt; {VV : [a] | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-definition'>descending</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt; a)}]&lt;\x1 VV -&gt; (VV &gt; a) &amp;&amp; (VV &gt; x1)&gt; | ((len VV) &gt; 0)}</span><span class='hs-keyword'>as</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>b</span><span class='hs-conop'>:</span><span class='hs-varid'>bs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>313: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x1:a
-&gt; x2:a
-&gt; {x4 : (Ordering) | ((x4 == GHC.Types.EQ) &lt;=&gt; (x1 == x2)) &amp;&amp; ((x4 == GHC.Types.GT) &lt;=&gt; (x1 &gt; x2)) &amp;&amp; ((x4 == GHC.Types.LT) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>`compare`</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>x1:(Ordering)
-&gt; x2:(Ordering) -&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 == x2))}</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Ordering) | (x3 == GHC.Types.GT) &amp;&amp; ((cmp x3) == GHC.Types.GT)}</span><span class='hs-conid'>GT</span></a> 
<span class=hs-linenum>314: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
a:a
-&gt; {VV : [{VV : a | (VV &gt; a)}]&lt;\x2 VV -&gt; (VV &gt; a) &amp;&amp; (VV &gt; x2)&gt; | ((len VV) &gt; 0)}
-&gt; {VV : [a] | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>descending</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:{VV : a | (VV &gt; b)}
-&gt; x2:[{VV : a&lt;p x1&gt; | (VV &gt; b)}]&lt;p&gt;
-&gt; {x4 : [{VV : a | (VV &gt; b)}]&lt;p&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) == (1 + (len x2))) &amp;&amp; ((sumLens x4) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{x5 : [{VV : a | (VV &gt; a)}]&lt;\x6 VV -&gt; (VV &gt; a) &amp;&amp; (VV &gt; x6)&gt; | (x5 == as) &amp;&amp; ((len x5) &gt; 0) &amp;&amp; ((len x5) &gt;= 0) &amp;&amp; ((sumLens x5) &gt;= 0)}</span><span class='hs-keyword'>as</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x4 : [a] | (x4 == bs) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>bs</span></a>
<span class=hs-linenum>315: </span><span class='hs-definition'>descending</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>as</span> <span class='hs-varid'>bs</span>      
<span class=hs-linenum>316: </span>  <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:{VV : a | (a &lt;= VV)}
-&gt; x2:[{VV : a&lt;p x1&gt; | (a &lt;= VV)}]&lt;p&gt;
-&gt; {x4 : [{VV : a | (a &lt;= VV)}]&lt;p&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) == (1 + (len x2))) &amp;&amp; ((sumLens x4) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{x5 : [{VV : a | (VV &gt; a)}]&lt;\x6 VV -&gt; (VV &gt; a) &amp;&amp; (VV &gt; x6)&gt; | (x5 == as) &amp;&amp; ((len x5) &gt; 0) &amp;&amp; ((len x5) &gt;= 0) &amp;&amp; ((sumLens x5) &gt;= 0)}</span><span class='hs-keyword'>as</span></a><span class='hs-layout'>)</span><a class=annot href="#"><span class=annottext>forall &lt;p :: [a]-&gt; [a]-&gt; Bool&gt;.
x1:{x15 : [a]&lt;\x16 VV -&gt; (x16 &lt;= VV)&gt; | ((len x15) &gt;= 0)}
-&gt; x2:[{x15 : [a]&lt;\x16 VV -&gt; (x16 &lt;= VV)&gt;&lt;p x1&gt; | ((len x15) &gt;= 0)}]&lt;p&gt;
-&gt; {x4 : [{x15 : [a]&lt;\x16 VV -&gt; (x16 &lt;= VV)&gt; | ((len x15) &gt;= 0)}]&lt;p&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) == (1 + (len x2))) &amp;&amp; ((sumLens x4) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
[a]
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>sequences</span></a> <a class=annot href="#"><span class=annottext>{x3 : [a] | ((len x3) &gt;= 0) &amp;&amp; ((sumLens x3) &gt;= 0)}</span><span class='hs-varid'>bs</span></a>
</pre>

Ex: `Data.List.sort` [3/4]
--------------------------

Juggling lists of increasing & decreasing lists

<br>



<pre><span class=hs-linenum>328: </span><a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
a:a
-&gt; (x1:{VV : [{VV : a | (VV &gt;= a)}]&lt;\x3 VV -&gt; (a &lt;= VV) &amp;&amp; (x3 &lt;= VV)&gt; | ((len VV) &gt; 0)}
    -&gt; {VV : [a]&lt;\x2 VV -&gt; (x2 &lt;= VV)&gt; | (VV /= x1) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len x1))})
-&gt; {VV : [a] | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-definition'>ascending</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x1:{VV : [{VV : a | (VV &gt;= a)}]&lt;\x2 VV -&gt; (a &lt;= VV) &amp;&amp; (x2 &lt;= VV)&gt; | ((len VV) &gt; 0)}
-&gt; {VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | (VV /= x1) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len x1))}</span><span class='hs-keyword'>as</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>b</span><span class='hs-conop'>:</span><span class='hs-varid'>bs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>329: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>x1:a
-&gt; x2:a
-&gt; {x4 : (Ordering) | ((x4 == GHC.Types.EQ) &lt;=&gt; (x1 == x2)) &amp;&amp; ((x4 == GHC.Types.GT) &lt;=&gt; (x1 &gt; x2)) &amp;&amp; ((x4 == GHC.Types.LT) &lt;=&gt; (x1 &lt; x2))}</span><span class='hs-varop'>`compare`</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>x1:(Ordering)
-&gt; x2:(Ordering) -&gt; {x2 : (Bool) | (((Prop x2)) &lt;=&gt; (x1 /= x2))}</span><span class='hs-varop'>/=</span></a> <a class=annot href="#"><span class=annottext>{x3 : (Ordering) | (x3 == GHC.Types.GT) &amp;&amp; ((cmp x3) == GHC.Types.GT)}</span><span class='hs-conid'>GT</span></a> 
<span class=hs-linenum>330: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
a:a
-&gt; (x1:{VV : [{VV : a | (VV &gt;= a)}]&lt;\x3 VV -&gt; (a &lt;= VV) &amp;&amp; (x3 &lt;= VV)&gt; | ((len VV) &gt; 0)}
    -&gt; {VV : [a]&lt;\x2 VV -&gt; (x2 &lt;= VV)&gt; | (VV /= x1) &amp;&amp; ((len VV) &gt; 0) &amp;&amp; ((len VV) &gt; (len x1))})
-&gt; {VV : [a] | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>ascending</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == b)}</span><span class='hs-varid'>b</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:{x7 : [{VV : a | (VV &gt;= a) &amp;&amp; (VV &gt;= b)}]&lt;\x8 VV -&gt; (a &lt;= VV) &amp;&amp; (b &lt;= VV) &amp;&amp; (x8 &lt;= VV)&gt; | ((len x7) &gt; 0)}
-&gt; {x4 : [a]&lt;\x5 VV -&gt; (VV &gt;= x5)&gt; | (x4 /= x1) &amp;&amp; ((len x4) &gt; 0) &amp;&amp; ((len x4) &gt; (len x1))}</span><span class='hs-keyglyph'>\</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= a) &amp;&amp; (VV &gt;= b)}]&lt;\x1 VV -&gt; (a &lt;= VV) &amp;&amp; (b &lt;= VV) &amp;&amp; (x1 &lt;= VV)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>ys</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>x1:{x7 : [{VV : a | (VV &gt;= a)}]&lt;\x8 VV -&gt; (a &lt;= VV) &amp;&amp; (x8 &lt;= VV)&gt; | ((len x7) &gt; 0)}
-&gt; {x4 : [a]&lt;\x5 VV -&gt; (x5 &lt;= VV)&gt; | (x4 /= x1) &amp;&amp; ((len x4) &gt; 0) &amp;&amp; ((len x4) &gt; (len x1))}</span><span class='hs-keyword'>as</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
x1:{VV : a | (VV &gt;= a)}
-&gt; x2:[{VV : a&lt;p x1&gt; | (VV &gt;= a)}]&lt;p&gt;
-&gt; {x4 : [{VV : a | (VV &gt;= a)}]&lt;p&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) == (1 + (len x2))) &amp;&amp; ((sumLens x4) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{x5 : [{VV : a | (VV &gt;= a) &amp;&amp; (VV &gt;= b)}]&lt;\x6 VV -&gt; (a &lt;= VV) &amp;&amp; (b &lt;= VV) &amp;&amp; (x6 &lt;= VV)&gt; | (x5 == ys) &amp;&amp; ((len x5) &gt; 0) &amp;&amp; ((len x5) &gt;= 0) &amp;&amp; ((sumLens x5) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{x4 : [a] | (x4 == bs) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>bs</span></a>
<span class=hs-linenum>331: </span><span class='hs-definition'>ascending</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>as</span> <span class='hs-varid'>bs</span>      
<span class=hs-linenum>332: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x7 : [{VV : a | (VV &gt;= a)}]&lt;\x8 VV -&gt; (a &lt;= VV) &amp;&amp; (x8 &lt;= VV)&gt; | ((len x7) &gt; 0)}
-&gt; {x4 : [a]&lt;\x5 VV -&gt; (x5 &lt;= VV)&gt; | (x4 /= x1) &amp;&amp; ((len x4) &gt; 0) &amp;&amp; ((len x4) &gt; (len x1))}</span><span class='hs-keyword'>as</span></a> <a class=annot href="#"><span class=annottext>{x4 : [{VV : a | (VV == a) &amp;&amp; (VV &gt; b)}]&lt;\_ VV -&gt; false&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV == a)}</span><span class='hs-varid'>a</span></a><span class='hs-keyglyph'>]</span><a class=annot href="#"><span class=annottext>forall &lt;p :: [a]-&gt; [a]-&gt; Bool&gt;.
x1:{x15 : [a]&lt;\x16 VV -&gt; (x16 &lt;= VV)&gt; | ((len x15) &gt;= 0)}
-&gt; x2:[{x15 : [a]&lt;\x16 VV -&gt; (x16 &lt;= VV)&gt;&lt;p x1&gt; | ((len x15) &gt;= 0)}]&lt;p&gt;
-&gt; {x4 : [{x15 : [a]&lt;\x16 VV -&gt; (x16 &lt;= VV)&gt; | ((len x15) &gt;= 0)}]&lt;p&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) == (1 + (len x2))) &amp;&amp; ((sumLens x4) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
[a]
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt; 0)}</span><span class='hs-varid'>sequences</span></a> <a class=annot href="#"><span class=annottext>{x3 : [a] | ((len x3) &gt;= 0) &amp;&amp; ((sumLens x3) &gt;= 0)}</span><span class='hs-varid'>bs</span></a>
</pre>

Ex: `Data.List.sort` [4/4]
--------------------------

Juggling lists of increasing & decreasing lists

<br>


<pre><span class=hs-linenum>343: </span><a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
{VV : [{VV : [a]&lt;\x2 VV -&gt; (x2 &lt;= VV)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0)}
-&gt; {VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0)}</span><span class='hs-definition'>mergeAll</span></a> <span class='hs-keyglyph'>[</span><span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x4 : [a]&lt;\x5 VV -&gt; (x5 &lt;= VV)&gt; | (x4 == x) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>344: </span><span class='hs-definition'>mergeAll</span> <span class='hs-varid'>xs</span>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
{VV : [{VV : [a]&lt;\x2 VV -&gt; (x2 &lt;= VV)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0)}
-&gt; {VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0)}</span><span class='hs-varid'>mergeAll</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:{x10 : [{x14 : [a]&lt;\x15 VV -&gt; (VV &gt;= x15)&gt; | ((len x14) &gt;= 0)}]&lt;\_ VV -&gt; ((len x12) &gt;= 0)&gt; | ((len x10) &gt;= 0)}
-&gt; {x3 : [{x7 : [a]&lt;\x8 VV -&gt; (VV &gt;= x8)&gt; | ((len x7) &gt;= 0)}]&lt;\_ VV -&gt; ((len x5) &gt;= 0)&gt; | ((len x3) &gt;= 0) &amp;&amp; ((len x3) &lt;= (len x1))}</span><span class='hs-varid'>mergePairs</span></a> <a class=annot href="#"><span class=annottext>{x3 : [{x7 : [a]&lt;\x8 VV -&gt; (x8 &lt;= VV)&gt; | ((len x7) &gt;= 0)}]&lt;\_ VV -&gt; ((len x5) &gt;= 0)&gt; | ((len x3) &gt;= 0) &amp;&amp; ((sumLens x3) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>345: </span>
<span class=hs-linenum>346: </span><a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
x1:{VV : [{VV : [a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))}</span><span class='hs-definition'>mergePairs</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>a</span><span class='hs-conop'>:</span><span class='hs-varid'>b</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{x10 : [a]&lt;\x11 VV -&gt; (VV &gt;= x11)&gt; | ((len x10) &gt;= 0)}
-&gt; x2:{x7 : [a]&lt;\x8 VV -&gt; (VV &gt;= x8)&gt; | ((len x7) &gt;= 0)}
-&gt; {x4 : [a]&lt;\x5 VV -&gt; (x5 &lt;= VV)&gt; | ((len x4) &gt;= 0) &amp;&amp; ((len x4) &gt;= (len x1)) &amp;&amp; ((len x4) &gt;= (len x2))}</span><span class='hs-varid'>merge</span></a> <a class=annot href="#"><span class=annottext>{x4 : [a]&lt;\x5 VV -&gt; (VV &gt;= x5)&gt; | (x4 == a) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{x4 : [a]&lt;\x5 VV -&gt; (VV &gt;= x5)&gt; | (x4 == b) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>b</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: [a]-&gt; [a]-&gt; Bool&gt;.
x1:{x15 : [a]&lt;\x16 VV -&gt; (VV &gt;= x16)&gt; | ((len x15) &gt;= 0)}
-&gt; x2:[{x15 : [a]&lt;\x16 VV -&gt; (VV &gt;= x16)&gt;&lt;p x1&gt; | ((len x15) &gt;= 0)}]&lt;p&gt;
-&gt; {x4 : [{x15 : [a]&lt;\x16 VV -&gt; (VV &gt;= x16)&gt; | ((len x15) &gt;= 0)}]&lt;p&gt; | (((null x4)) &lt;=&gt; false) &amp;&amp; ((len x4) == (1 + (len x2))) &amp;&amp; ((sumLens x4) == ((len x1) + (sumLens x2)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
(Ord a) =&gt;
x1:{VV : [{VV : [a]&lt;\x2 VV -&gt; (VV &gt;= x2)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0)}
-&gt; {VV : [{VV : [a]&lt;\x1 VV -&gt; (x1 &lt;= VV)&gt; | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | ((len VV) &gt;= 0) &amp;&amp; ((len VV) &lt;= (len x1))}</span><span class='hs-varid'>mergePairs</span></a> <a class=annot href="#"><span class=annottext>{x4 : [{x8 : [a]&lt;\x9 VV -&gt; (VV &gt;= x9)&gt; | ((len x8) &gt;= 0)}]&lt;\_ VV -&gt; ((len x6) &gt;= 0)&gt; | (x4 == xs) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>347: </span><span class='hs-definition'>mergePairs</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{x6 : [{x8 : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | false}]&lt;\_ VV -&gt; false&gt; | (((null x6)) &lt;=&gt; true) &amp;&amp; ((len x6) == 0) &amp;&amp; ((sumLens x6) == 0) &amp;&amp; ((len x6) &gt;= 0) &amp;&amp; ((sumLens x6) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{x4 : [a]&lt;\x5 VV -&gt; (VV &gt;= x5)&gt; | (x4 == a) &amp;&amp; ((len x4) &gt;= 0) &amp;&amp; ((sumLens x4) &gt;= 0)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>348: </span><span class='hs-definition'>mergePairs</span> <span class='hs-conid'>[]</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: [a]-&gt; [a]-&gt; Bool&gt;.
{x4 : [{x6 : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | false}]&lt;p&gt; | (((null x4)) &lt;=&gt; true) &amp;&amp; ((len x4) == 0) &amp;&amp; ((sumLens x4) == 0)}</span><span class='hs-conid'>[]</span></a>
</pre>

Phew!
-----

Lets see one last example...


Example: Binary Trees
---------------------

... `Map` from keys of type `k` to values of type `a` 

<br>

<div class="fragment">

Implemented, in `Data.Map` as a binary tree:

<br>


<pre><span class=hs-linenum>371: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>Map</span> <span class='hs-varid'>k</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Tip</span>
<span class=hs-linenum>372: </span>             <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Bin</span> <span class='hs-conid'>Size</span> <span class='hs-varid'>k</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-conid'>Map</span> <span class='hs-varid'>k</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-conid'>Map</span> <span class='hs-varid'>k</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>373: </span>
<span class=hs-linenum>374: </span><span class='hs-keyword'>type</span> <span class='hs-conid'>Size</span>    <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Int</span>
</pre>
</div>

Two Abstract Refinements
------------------------

- `l` : relates root `key` with `left`-subtree keys
- `r` : relates root `key` with `right`-subtree keys


<pre><span class=hs-linenum>385: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>Map</span> <span class='hs-varid'>k</span> <span class='hs-varid'>a</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>l</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>k</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>k</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span>
<span class=hs-linenum>386: </span>                 <span class='hs-layout'>,</span> <span class='hs-varid'>r</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>k</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>k</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span> <span class='hs-varop'>&gt;</span>
<span class=hs-linenum>387: </span>    <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Tip</span>
<span class=hs-linenum>388: </span>    <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Bin</span> <span class='hs-layout'>(</span><span class='hs-varid'>sz</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Size</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>key</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>k</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>val</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>389: </span>          <span class='hs-layout'>(</span><span class='hs-varid'>left</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Map</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>l</span><span class='hs-layout'>,</span><span class='hs-varid'>r</span><span class='hs-varop'>&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>k</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>l</span> <span class='hs-varid'>key</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>390: </span>          <span class='hs-layout'>(</span><span class='hs-varid'>right</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Map</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>l</span><span class='hs-layout'>,</span><span class='hs-varid'>r</span><span class='hs-varop'>&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>k</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>r</span> <span class='hs-varid'>key</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>


Ex: Binary Search Trees
-----------------------

Keys are *Binary-Search* Ordered

<br>


<pre><span class=hs-linenum>402: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>BST</span> <span class='hs-varid'>k</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> 
<span class=hs-linenum>403: </span>      <span class='hs-conid'>Map</span> <span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>r</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>r</span> <span class='hs-layout'>}</span><span class='hs-layout'>,</span> 
<span class=hs-linenum>404: </span>           <span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>r</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&gt;</span> <span class='hs-varid'>r</span> <span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>405: </span>          <span class='hs-varid'>k</span> <span class='hs-varid'>a</span>                   <span class='hs-keyword'>@-}</span>
</pre>

Ex: Minimum Heaps 
-----------------

Root contains *minimum* value

<br>


<pre><span class=hs-linenum>416: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>MinHeap</span> <span class='hs-varid'>k</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> 
<span class=hs-linenum>417: </span>      <span class='hs-conid'>Map</span> <span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>r</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>r</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span><span class='hs-layout'>,</span> 
<span class=hs-linenum>418: </span>           <span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>r</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>r</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>419: </span>           <span class='hs-varid'>k</span> <span class='hs-varid'>a</span>               <span class='hs-keyword'>@-}</span>
</pre>

Ex: Maximum Heaps 
-----------------

Root contains *maximum* value

<br>


<pre><span class=hs-linenum>430: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>MaxHeap</span> <span class='hs-varid'>k</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> 
<span class=hs-linenum>431: </span>      <span class='hs-conid'>Map</span> <span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>r</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>r</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span><span class='hs-layout'>,</span> 
<span class=hs-linenum>432: </span>           <span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>r</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>r</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>433: </span>           <span class='hs-varid'>k</span> <span class='hs-varid'>a</span>               <span class='hs-keyword'>@-}</span>
</pre>


Example: Data.Map
-----------------

Standard Key-Value container

- <div class="fragment">1300+ non-comment lines</div>

- <div class="fragment">`insert`, `split`, `merge`,...</div>

- <div class="fragment">Rotation, Rebalance,...</div>

<div class="fragment">
SMT & inference crucial for [verification](https://github.com/ucsd-progsys/liquidhaskell/blob/master/benchmarks/esop2013-submission/Base.hs)
</div>

<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=Map.hs" target="_blank">Demo:</a>Try online!
</div>

Recap: Abstract Refinements
---------------------------

<div class="fragment">

Decouple invariants from *functions*

+ `max`
+ `loop`
+ `foldr`

</div>

<div class="fragment">
Decouple invariants from *data*

+ `Vector`
+ `List`
+ `Tree`

</div>


Recap
-----

1. **Refinements:** Types + Predicates
2. **Subtyping:** SMT Implication
3. **Measures:** Strengthened Constructors
4. **Abstract Refinements:* Decouple Invariants 
5. <div class="fragment">Er, what of *lazy evaluation*?</div>
