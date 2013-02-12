---
layout: post
title: "Index-Dependent Maps"
date: 2013-01-20 16:12
comments: true
external-url:
categories: abstract-refinement, basic
author: Niki Vazou
published: false
---

In this example, we illustrate how abstract invariants allow us to specify
and verify index-dependent invariants of key-value maps.  To this end, we
develop a small library of _extensible vectors_ encoded, for purposes of
illustration, as functions from `Int` to some generic range `a`. 


<pre><span class=hs-linenum>18: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>LiquidArray</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>19: </span>
<span class=hs-linenum>20: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span> <span class='hs-layout'>(</span><span class='hs-varid'>liquidAssume</span><span class='hs-layout'>)</span>
</pre>

We specify vectors as 
<pre><span class=hs-linenum>24: </span><span class='hs-keyword'>type</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>dom</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-layout'>,</span> <span class='hs-varid'>rng</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;</span>
<span class=hs-linenum>25: </span>  <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>dom</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>rng</span> <span class='hs-varid'>i</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span>
</pre>


<pre><span class=hs-linenum>29: </span><span class='hs-keyword'>type</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
</pre>

Here, we are parametrizing the definition of the type `Vec` with _two_ abstract refinements, `dom` and `rng`, which respectively describe the _domain_ and _range_ of the vector.
That is, `dom` describes the set of _valid_ indices, and `rng` specifies an invariant relating each `Int` index with the value stored at that index.

Creating Vectors
----------------

We can use the following basic functions to create vectors:


<pre><span class=hs-linenum>41: </span><span class='hs-comment'>{- empty :: forall &lt;rng :: Int -&gt; a -&gt; Prop&gt;. 
              i:{v: Int | 0 = 1} -&gt;  a&lt;rng&gt; -}</span>
<span class=hs-linenum>43: </span>
<span class=hs-linenum>44: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>empty</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| 0 = 1}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>45: </span><span class='hs-definition'>empty</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>46: </span><a class=annot href="#"><span class=annottext>forall a. {VV : (Int) | false} -&gt; a</span><span class='hs-definition'>empty</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | false} -&gt; {VV : a | false}</span><span class='hs-keyglyph'>\</span></a><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>[(Char)] -&gt; {VV : a | false}</span><span class='hs-varid'>error</span></a> <a class=annot href="#"><span class=annottext>{VV : [(Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"Empty Vec"</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>47: </span>
<span class=hs-linenum>48: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>create</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-definition'>a</span> <span class='hs-keyword'>| v = x}</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>49: </span><span class='hs-definition'>create</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>50: </span><a class=annot href="#"><span class=annottext>forall a. x:a -&gt; (Int) -&gt; {VV : a | (VV = x)}</span><span class='hs-definition'>create</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-keyglyph'>\</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span>
</pre>

The signature for `empty` states that its domain is empty (ie is the set of indices satisfying the predicate `False`), and that the range satisfies _any_ invariant. The signature for `create`, instead, defines a _constant_ vector that maps every index to the constant `x`.

Accessing Vectors
-----------------

We can write the following `get` function for reading the contents of a vector at a given index:


<pre><span class=hs-linenum>61: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>get</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>d</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x0</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-layout'>,</span> <span class='hs-varid'>r</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x0</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x1</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span>
<span class=hs-linenum>62: </span>             <span class='hs-varid'>i</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>d</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>63: </span>             <span class='hs-varid'>a</span><span class='hs-conop'>:</span> <span class='hs-layout'>(</span><span class='hs-varid'>j</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>d</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>r</span> <span class='hs-varid'>j</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>64: </span>             <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>r</span> <span class='hs-varid'>i</span><span class='hs-varop'>&gt;</span> 
<span class=hs-linenum>65: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>66: </span><span class='hs-definition'>get</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>67: </span><a class=annot href="#"><span class=annottext>forall a &lt;d :: (Int) -&gt; Bool , r :: (Int) -&gt; a -&gt; Bool&gt;.
i:(Int)&lt;d 0&gt;
-&gt; (j:(Int)&lt;d 0&gt; -&gt; a&lt;r (x0, EVar j) 1&gt;) -&gt; a&lt;r (x0, EVar i) 1&gt;</span><span class='hs-definition'>get</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((x0 = (x0 - 1)) =&gt; (VV = 0)),(? papp1([d; VV]))}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x0 = (x0 - 1)) =&gt; (VV = 0)),
                 (? papp1([d; VV])),
                 (VV = i)}
-&gt; {VV : a | (? papp2([r; VV; i])),(? papp2([r; VV; x1]))}</span><span class='hs-varid'>a</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x0 = (x0 - 1)) =&gt; (VV = 0)),
                 (? papp1([d; VV])),
                 (VV = i)}
-&gt; {VV : a | (? papp2([r; VV; i])),(? papp2([r; VV; x1]))}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((x0 = (x0 - 1)) =&gt; (VV = 0)),
              (? papp1([d; VV])),
              (VV = i)}</span><span class='hs-varid'>i</span></a>
</pre>

The signature states that for any domain `d` and range `r`, if the index `i` is a valid index, ie is of type, `Int<d>` then the returned value is an `a` that additionally satisfies the range refinement at the index `i`.

The type for `set`, which _updates_ the vector at a given index, is even more interesting, as it allows us to _extend_ the domain of the vector:


<pre><span class=hs-linenum>75: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>set</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>r</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x0</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x1</span><span class='hs-conop'>:</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-layout'>,</span> <span class='hs-varid'>d</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x0</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span>
<span class=hs-linenum>76: </span>      <span class='hs-varid'>i</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>d</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>77: </span>      <span class='hs-varid'>x</span><span class='hs-conop'>:</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>r</span> <span class='hs-varid'>i</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>78: </span>      <span class='hs-varid'>a</span><span class='hs-conop'>:</span> <span class='hs-layout'>(</span><span class='hs-varid'>j</span><span class='hs-conop'>:</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>d</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>| v != i}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>r</span> <span class='hs-varid'>j</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>79: </span>      <span class='hs-layout'>(</span><span class='hs-varid'>k</span> <span class='hs-conop'>:</span> <span class='hs-conid'>Int</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>d</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>r</span> <span class='hs-varid'>k</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span>
<span class=hs-linenum>80: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>81: </span><span class='hs-definition'>set</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>82: </span><a class=annot href="#"><span class=annottext>forall a &lt;r :: (Int) -&gt; a -&gt; Bool , d :: (Int) -&gt; Bool&gt;.
i:(Int)&lt;d 0&gt;
-&gt; a&lt;r (x0, EVar i) 1&gt;
-&gt; (j:{VV : (Int)&lt;d 0&gt; | (VV != i)} -&gt; a&lt;r (x0, EVar j) 1&gt;)
-&gt; k:(Int)&lt;d 0&gt;
-&gt; a&lt;r (x0, EVar k) 1&gt;</span><span class='hs-definition'>set</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((x0 = (x0 - 1)) =&gt; (VV = 0)),(? papp1([d; VV]))}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (? papp2([r; VV; i]))}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x0 = (x0 - 1)) =&gt; (VV = 0)),
                 (? papp1([d; VV])),
                 (VV != i)}
-&gt; {VV : a | (? papp2([r; VV; x1]))}</span><span class='hs-varid'>a</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>\</span><a class=annot href="#"><span class=annottext>{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
              ((x0 = (x0 - 1)) =&gt; (VV = 0)),
              (? papp1([d; VV]))}</span><span class='hs-varid'>k</span></a> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>if</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
              ((x0 = (x0 - 1)) =&gt; (VV = 0)),
              (? papp1([d; VV])),
              (VV = k)}</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                ((k = (k - 1)) =&gt; (VV = 0)),
                ((x0 = (x0 - 1)) =&gt; (VV = 0)),
                (? papp1([d; VV]))}
-&gt; y:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                   ((k = (k - 1)) =&gt; (VV = 0)),
                   ((x0 = (x0 - 1)) =&gt; (VV = 0)),
                   (? papp1([d; VV]))}
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x = y))}</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((x0 = (x0 - 1)) =&gt; (VV = 0)),
              (? papp1([d; VV])),
              (VV = i)}</span><span class='hs-varid'>i</span></a> <span class='hs-keyword'>then</span> <a class=annot href="#"><span class=annottext>{VV : a | (? papp2([r; VV; i])),(VV = x)}</span><span class='hs-varid'>x</span></a> <span class='hs-keyword'>else</span> <a class=annot href="#"><span class=annottext>x1:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x0 = (x0 - 1)) =&gt; (VV = 0)),
                 (? papp1([d; VV])),
                 (VV != i)}
-&gt; {VV : a | (? papp2([r; VV; x1]))}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
              ((x0 = (x0 - 1)) =&gt; (VV = 0)),
              (? papp1([d; VV])),
              (VV = k)}</span><span class='hs-varid'>k</span></a>
</pre>

The signature for `set` requires that (a) the input vector is defined everywhere at `d` _except_ the index `i`, and (b) the value supplied must be of type `a<r i>`, ie satisfy the range relation at the index `i` at which the vector is being updated.
The signature ensures that the output vector is defined at `d` and each value satisfies the index-dependent range refinement `r`.

Note that it is legal to call `get` with a vector that is _also_ defined at the index `i` since, by contravariance, such a vector is a subtype of that required by (a).


Initializing Vectors
--------------------

Next, we can write the following function, `init`, that ''loops'' over a vector, to `set` each index to a value given by some function.


<pre><span class=hs-linenum>97: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>initialize</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>r</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x0</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x1</span><span class='hs-conop'>:</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span>
<span class=hs-linenum>98: </span>      <span class='hs-varid'>f</span><span class='hs-conop'>:</span> <span class='hs-layout'>(</span><span class='hs-varid'>z</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>r</span> <span class='hs-varid'>z</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>99: </span>      <span class='hs-varid'>i</span><span class='hs-conop'>:</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| v &gt;= 0}</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>100: </span>      <span class='hs-varid'>n</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>101: </span>      <span class='hs-varid'>a</span><span class='hs-conop'>:</span> <span class='hs-layout'>(</span><span class='hs-varid'>j</span><span class='hs-conop'>:</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| (0 &lt;= v &amp;&amp; v &lt; i)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>r</span> <span class='hs-varid'>j</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>102: </span>      <span class='hs-layout'>(</span><span class='hs-varid'>k</span><span class='hs-conop'>:</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| (0 &lt;= v &amp;&amp; v &lt; n)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>r</span> <span class='hs-varid'>k</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>103: </span><span class='hs-definition'>initialize</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>104: </span><a class=annot href="#"><span class=annottext>forall a &lt;r :: (Int) -&gt; a -&gt; Bool&gt;.
(z:(Int) -&gt; a&lt;r (x0, EVar z) 1&gt;)
-&gt; i:{VV : (Int) | (VV &gt;= 0)}
-&gt; n:(Int)
-&gt; (j:{VV : (Int) | (VV &lt; i),(0 &lt;= VV)} -&gt; a&lt;r (x0, EVar j) 1&gt;)
-&gt; k:{VV : (Int) | (VV &lt; n),(0 &lt;= VV)}
-&gt; a&lt;r (x0, EVar k) 1&gt;</span><span class='hs-definition'>initialize</span></a> <a class=annot href="#"><span class=annottext>x1:{VV : (Int) | ((x0 = (x0 - 1)) =&gt; (VV = 0))}
-&gt; {VV : a | (? papp2([r; VV; x1]))}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((x0 = (x0 - 1)) =&gt; (VV = 0)),(VV &gt;= 0),(0 &lt;= VV)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
              ((x0 = (x0 - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x1:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0)),
                 ((x0 = (x0 - 1)) =&gt; (VV = 0)),
                 (VV &gt;= 0),
                 (VV &lt; i),
                 (VV &lt; n),
                 (0 &lt;= VV)}
-&gt; {VV : a | (? papp2([r; VV; x1]))}</span><span class='hs-varid'>a</span></a> 
<span class=hs-linenum>105: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((x0 = (x0 - 1)) =&gt; (VV = 0)),
              (VV = i),
              (VV &gt;= 0),
              (0 &lt;= VV)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                ((n = (n - 1)) =&gt; (VV = 0)),
                ((x0 = (x0 - 1)) =&gt; (VV = 0))}
-&gt; y:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                   ((n = (n - 1)) =&gt; (VV = 0)),
                   ((x0 = (x0 - 1)) =&gt; (VV = 0))}
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x &gt;= y))}</span><span class='hs-varop'>&gt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
              ((x0 = (x0 - 1)) =&gt; (VV = 0)),
              (VV = n)}</span><span class='hs-varid'>n</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0)),
                 ((x0 = (x0 - 1)) =&gt; (VV = 0)),
                 (VV &gt;= 0),
                 (VV &lt; i),
                 (VV &lt; n),
                 (0 &lt;= VV)}
-&gt; {VV : a | (? papp2([r; VV; x1]))}</span><span class='hs-varid'>a</span></a>
<span class=hs-linenum>106: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;r :: (Int) -&gt; a -&gt; Bool&gt;.
(z:(Int) -&gt; a&lt;r (x0, EVar z) 1&gt;)
-&gt; i:{VV : (Int) | (VV &gt;= 0)}
-&gt; n:(Int)
-&gt; (j:{VV : (Int) | (VV &lt; i),(0 &lt;= VV)} -&gt; a&lt;r (x0, EVar j) 1&gt;)
-&gt; k:{VV : (Int) | (VV &lt; n),(0 &lt;= VV)}
-&gt; a&lt;r (x0, EVar k) 1&gt;</span><span class='hs-varid'>initialize</span></a> <a class=annot href="#"><span class=annottext>x1:{VV : (Int) | ((x0 = (x0 - 1)) =&gt; (VV = 0))}
-&gt; {VV : a | (? papp2([r; VV; x1]))}</span><span class='hs-varid'>f</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Int) | ((x0 = (x0 - 1)) =&gt; (VV = 0)),
              (VV = i),
              (VV &gt;= 0),
              (0 &lt;= VV)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x:(Int) -&gt; y:(Int) -&gt; {VV : (Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
              ((x0 = (x0 - 1)) =&gt; (VV = 0)),
              (VV = n)}</span><span class='hs-varid'>n</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall &lt;d :: (Int) -&gt; Bool , r :: (Int) -&gt; a -&gt; Bool&gt;.
i:(Int)&lt;d 0&gt;
-&gt; a&lt;r (x0, EVar i) 1&gt;
-&gt; (j:{VV : (Int)&lt;d 0&gt; | (VV != i)} -&gt; a&lt;r (x0, EVar j) 1&gt;)
-&gt; k:(Int)&lt;d 0&gt;
-&gt; a&lt;r (x0, EVar k) 1&gt;</span><span class='hs-varid'>set</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((x0 = (x0 - 1)) =&gt; (VV = 0)),
              (VV = i),
              (VV &gt;= 0),
              (0 &lt;= VV)}</span><span class='hs-varid'>i</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:{VV : (Int) | ((x0 = (x0 - 1)) =&gt; (VV = 0))}
-&gt; {VV : a | (? papp2([r; VV; x1]))}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((x0 = (x0 - 1)) =&gt; (VV = 0)),
              (VV = i),
              (VV &gt;= 0),
              (0 &lt;= VV)}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x1:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0)),
                 ((x0 = (x0 - 1)) =&gt; (VV = 0)),
                 (VV &gt;= 0),
                 (VV &lt; i),
                 (VV &lt; n),
                 (0 &lt;= VV)}
-&gt; {VV : a | (? papp2([r; VV; x1]))}</span><span class='hs-varid'>a</span></a><span class='hs-layout'>)</span>
</pre>

The signature requires that (a) the higher-order function `f` produces values that satisfy the range refinement `r`, and (b) the vector is initialized from `0` to `i`.
The function ensures that the output vector is initialized from `0`
through `n`.

We can thus verify that


<pre><span class=hs-linenum>116: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>idVec</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>k</span><span class='hs-conop'>:</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| (0 &lt;= v &amp;&amp; v &lt; n)}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = k}</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>117: </span><span class='hs-definition'>idVec</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Vec</span> <span class='hs-conid'>Int</span><span class='hs-layout'>)</span>
<span class=hs-linenum>118: </span><a class=annot href="#"><span class=annottext>n:(Int)
-&gt; k:{VV : (Int) | (VV &lt; n),(0 &lt;= VV)} -&gt; {VV : (Int) | (VV = k)}</span><span class='hs-definition'>idVec</span></a> <a class=annot href="#"><span class=annottext>(Int)</span><span class='hs-varid'>n</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;r :: (Int) -&gt; (Int) -&gt; Bool&gt;.
(z:(Int)
 -&gt; {VV : (Int)&lt;r (x0, EVar z) 1&gt; | ((n = (n - 1)) =&gt; (VV = 0))})
-&gt; i:{VV : (Int) | (VV &gt;= 0)}
-&gt; n:(Int)
-&gt; (j:{VV : (Int) | (VV &lt; i),(0 &lt;= VV)}
    -&gt; {VV : (Int)&lt;r (x0, EVar j) 1&gt; | ((n = (n - 1)) =&gt; (VV = 0))})
-&gt; k:{VV : (Int) | (VV &lt; n),(0 &lt;= VV)}
-&gt; {VV : (Int)&lt;r (x0, EVar k) 1&gt; | ((n = (n - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>initialize</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>i:{VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0))}
-&gt; {VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),(VV = i)}</span><span class='hs-keyglyph'>\</span></a><a class=annot href="#"><span class=annottext>{VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>i</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),(VV = i)}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = n)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | false} -&gt; {VV : (Int) | false}</span><span class='hs-varid'>empty</span></a>
</pre>

ie `idVec` returns an vector of size `n` where each key is mapped to itself. Thus, abstract refinement types allow us to verify low-level idioms such as the incremental initialization of vectors, which have previously required special analyses.

Null-Terminated Strings
-----------------------

We can also use abstract refinements to verify code which manipulates C-style null-terminated strings, where each character is represented as an `Int` and the termination character `\0`, and only that, is represented as `0`.

Formally, a null-terminated string, represented by `Int`s, of size `n` has the type
<pre><span class=hs-linenum>129: </span><span class='hs-keyword'>type</span> <span class='hs-conid'>NullTerm</span> <span class='hs-varid'>n</span> 
<span class=hs-linenum>130: </span>     <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Vec</span> <span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-num'>0</span><span class='hs-varop'>&lt;=</span><span class='hs-varid'>v</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>n</span><span class='hs-layout'>}</span><span class='hs-layout'>,</span> <span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>i</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>i</span><span class='hs-keyglyph'>=</span><span class='hs-varid'>n</span><span class='hs-comment'>-</span><span class='hs-num'>1</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>v</span><span class='hs-keyglyph'>=</span><span class='hs-num'>0</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> <span class='hs-conid'>Int</span>
</pre>

The above type describes a length-`n` vector of characters whose last element must be a null character, signalling the end of the string.

We can use this type in the specification of a function, `upperCase`, which iterates through the characters of a string, uppercasing each one until it encounters the null terminator:


<pre><span class=hs-linenum>138: </span><span class='hs-definition'>ucs</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Vec</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Vec</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>139: </span><a class=annot href="#"><span class=annottext>n:{VV : (Int) | (VV &gt; 0)}
-&gt; i:{VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),
                   (VV &gt;= 0),
                   (VV &lt; n),
                   (0 &lt;= VV)}
-&gt; (x8:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                     ((n = (i - 1)) =&gt; (VV = 0)),
                     ((n = (n - 1)) =&gt; (VV = 0)),
                     (VV &gt;= 0),
                     (VV &lt; n),
                     (0 &lt;= VV)}
    -&gt; {VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                     ((x8 = (x8 - 1)) =&gt; (VV = 0)),
                     ((x8 = (n - 1)) =&gt; (VV = 0)),
                     ((n = (i - 1)) =&gt; (VV = 0)),
                     ((n = (x8 - 1)) =&gt; (VV = 0)),
                     ((n = (n - 1)) =&gt; (VV = 0))})
-&gt; x4:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                    ((n = (i - 1)) =&gt; (VV = 0)),
                    ((n = (n - 1)) =&gt; (VV = 0)),
                    (VV &gt;= 0),
                    (VV &lt; n)}
-&gt; {VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x4 = (x4 - 1)) =&gt; (VV = 0)),
                 ((x4 = (n - 1)) =&gt; (VV = 0)),
                 ((n = (i - 1)) =&gt; (VV = 0)),
                 ((n = (x4 - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0))}</span><span class='hs-definition'>ucs</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt; 0)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),
              (VV &gt;= 0),
              (VV &lt; n),
              (0 &lt;= VV)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x4:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((n = (i - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0)),
                 (VV &gt;= 0),
                 (VV &lt; n)}
-&gt; {VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x4 = (x4 - 1)) =&gt; (VV = 0)),
                 ((x4 = (n - 1)) =&gt; (VV = 0)),
                 ((n = (i - 1)) =&gt; (VV = 0)),
                 ((n = (x4 - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>s</span></a> <span class='hs-keyglyph'>=</span>
<span class=hs-linenum>140: </span>  <span class='hs-keyword'>case</span> <a class=annot href="#"><span class=annottext>forall &lt;r :: (Int) -&gt; (Int) -&gt; Bool , d :: (Int) -&gt; Bool&gt;.
i:(Int)&lt;d 0&gt;
-&gt; (j:(Int)&lt;d 0&gt;
    -&gt; {VV : (Int)&lt;r (x0, EVar j) 1&gt; | ((i = (i - 1)) =&gt; (VV = 0)),
                                       ((i = (n - 1)) =&gt; (VV = 0)),
                                       ((n = (i - 1)) =&gt; (VV = 0)),
                                       ((n = (n - 1)) =&gt; (VV = 0))})
-&gt; {VV : (Int)&lt;r (x0, EVar i) 1&gt; | ((i = (i - 1)) =&gt; (VV = 0)),
                                   ((i = (n - 1)) =&gt; (VV = 0)),
                                   ((n = (i - 1)) =&gt; (VV = 0)),
                                   ((n = (n - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>get</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),
              (VV = i),
              (VV &gt;= 0),
              (VV &lt; n),
              (0 &lt;= VV)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x4:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((n = (i - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0)),
                 (VV &gt;= 0),
                 (VV &lt; n)}
-&gt; {VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x4 = (x4 - 1)) =&gt; (VV = 0)),
                 ((x4 = (n - 1)) =&gt; (VV = 0)),
                 ((n = (i - 1)) =&gt; (VV = 0)),
                 ((n = (x4 - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>s</span></a> <span class='hs-keyword'>of</span>
<span class=hs-linenum>141: </span>  <span class='hs-num'>0</span> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>x4:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((n = (i - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0)),
                 (VV &gt;= 0),
                 (VV &lt; n)}
-&gt; {VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x4 = (x4 - 1)) =&gt; (VV = 0)),
                 ((x4 = (n - 1)) =&gt; (VV = 0)),
                 ((n = (i - 1)) =&gt; (VV = 0)),
                 ((n = (x4 - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>s</span></a>
<span class=hs-linenum>142: </span>  <span class='hs-varid'>c</span> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>n:{VV : (Int) | (VV &gt; 0)}
-&gt; i:{VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),
                   (VV &gt;= 0),
                   (VV &lt; n),
                   (0 &lt;= VV)}
-&gt; (x8:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                     ((n = (i - 1)) =&gt; (VV = 0)),
                     ((n = (n - 1)) =&gt; (VV = 0)),
                     (VV &gt;= 0),
                     (VV &lt; n),
                     (0 &lt;= VV)}
    -&gt; {VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                     ((x8 = (x8 - 1)) =&gt; (VV = 0)),
                     ((x8 = (n - 1)) =&gt; (VV = 0)),
                     ((n = (i - 1)) =&gt; (VV = 0)),
                     ((n = (x8 - 1)) =&gt; (VV = 0)),
                     ((n = (n - 1)) =&gt; (VV = 0))})
-&gt; x4:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                    ((n = (i - 1)) =&gt; (VV = 0)),
                    ((n = (n - 1)) =&gt; (VV = 0)),
                    (VV &gt;= 0),
                    (VV &lt; n)}
-&gt; {VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x4 = (x4 - 1)) =&gt; (VV = 0)),
                 ((x4 = (n - 1)) =&gt; (VV = 0)),
                 ((n = (i - 1)) =&gt; (VV = 0)),
                 ((n = (x4 - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>ucs</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = n),(VV &gt; 0)}</span><span class='hs-varid'>n</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),
              (VV = i),
              (VV &gt;= 0),
              (VV &lt; n),
              (0 &lt;= VV)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x:(Int) -&gt; y:(Int) -&gt; {VV : (Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall &lt;d :: (Int) -&gt; Bool , r :: (Int) -&gt; (Int) -&gt; Bool&gt;.
i:(Int)&lt;d 0&gt;
-&gt; {VV : (Int)&lt;r (x0,
                  EVar i) 1&gt; | ((ds_dCA = (ds_dCA - 1)) =&gt; (VV = 0)),
                               ((ds_dCA = (ds_dCz - 1)) =&gt; (VV = 0)),
                               ((ds_dCz = (ds_dCA - 1)) =&gt; (VV = 0)),
                               ((ds_dCz = (ds_dCz - 1)) =&gt; (VV = 0)),
                               ((i = (i - 1)) =&gt; (VV = 0)),
                               ((i = (n - 1)) =&gt; (VV = 0)),
                               ((n = (i - 1)) =&gt; (VV = 0)),
                               ((n = (n - 1)) =&gt; (VV = 0))}
-&gt; (j:{VV : (Int)&lt;d 0&gt; | (VV != i)}
    -&gt; {VV : (Int)&lt;r (x0,
                      EVar j) 1&gt; | ((ds_dCA = (ds_dCA - 1)) =&gt; (VV = 0)),
                                   ((ds_dCA = (ds_dCz - 1)) =&gt; (VV = 0)),
                                   ((ds_dCz = (ds_dCA - 1)) =&gt; (VV = 0)),
                                   ((ds_dCz = (ds_dCz - 1)) =&gt; (VV = 0)),
                                   ((i = (i - 1)) =&gt; (VV = 0)),
                                   ((i = (n - 1)) =&gt; (VV = 0)),
                                   ((n = (i - 1)) =&gt; (VV = 0)),
                                   ((n = (n - 1)) =&gt; (VV = 0))})
-&gt; k:(Int)&lt;d 0&gt;
-&gt; {VV : (Int)&lt;r (x0,
                  EVar k) 1&gt; | ((ds_dCA = (ds_dCA - 1)) =&gt; (VV = 0)),
                               ((ds_dCA = (ds_dCz - 1)) =&gt; (VV = 0)),
                               ((ds_dCz = (ds_dCA - 1)) =&gt; (VV = 0)),
                               ((ds_dCz = (ds_dCz - 1)) =&gt; (VV = 0)),
                               ((i = (i - 1)) =&gt; (VV = 0)),
                               ((i = (n - 1)) =&gt; (VV = 0)),
                               ((n = (i - 1)) =&gt; (VV = 0)),
                               ((n = (n - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>set</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),
              (VV = i),
              (VV &gt;= 0),
              (VV &lt; n),
              (0 &lt;= VV)}</span><span class='hs-varid'>i</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
              ((i = (n - 1)) =&gt; (VV = 0)),
              ((n = (i - 1)) =&gt; (VV = 0)),
              ((n = (n - 1)) =&gt; (VV = 0)),
              (VV = ds_dCz)}</span><span class='hs-varid'>c</span></a> <a class=annot href="#"><span class=annottext>x:(Int) -&gt; y:(Int) -&gt; {VV : (Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (32  :  int))}</span><span class='hs-num'>32</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x4:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((n = (i - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0)),
                 (VV &gt;= 0),
                 (VV &lt; n)}
-&gt; {VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x4 = (x4 - 1)) =&gt; (VV = 0)),
                 ((x4 = (n - 1)) =&gt; (VV = 0)),
                 ((n = (i - 1)) =&gt; (VV = 0)),
                 ((n = (x4 - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>s</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>143: </span>
<span class=hs-linenum>144: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>upperCaseString</span> <span class='hs-keyglyph'>::</span>
<span class=hs-linenum>145: </span>      <span class='hs-varid'>n</span><span class='hs-conop'>:</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| v &gt; 0}</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>146: </span>      <span class='hs-varid'>s</span><span class='hs-conop'>:</span> <span class='hs-layout'>(</span><span class='hs-varid'>j</span><span class='hs-conop'>:</span> <span class='hs-keyword'>{v :</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| (0 &lt;= v &amp;&amp; v &lt; n)}</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>147: </span>          <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| (j = n - 1 =&gt; v = 0)}</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>148: </span>      <span class='hs-layout'>(</span><span class='hs-varid'>j</span><span class='hs-conop'>:</span> <span class='hs-keyword'>{v :</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| (0 &lt;= v &amp;&amp; v &lt; n)}</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>149: </span>       <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| (j = n - 1 =&gt; v = 0)}</span><span class='hs-layout'>)</span>
<span class=hs-linenum>150: </span><span class='hs-keyword'>@-}</span>
<span class=hs-linenum>151: </span><span class='hs-definition'>upperCaseString</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Vec</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Vec</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>152: </span><a class=annot href="#"><span class=annottext>n:{VV : (Int) | (VV &gt; 0)}
-&gt; (j:{VV : (Int) | (VV &lt; n),(0 &lt;= VV)}
    -&gt; {VV : (Int) | ((j = (n - 1)) =&gt; (VV = 0))})
-&gt; j:{VV : (Int) | (VV &lt; n),(0 &lt;= VV)}
-&gt; {VV : (Int) | ((j = (n - 1)) =&gt; (VV = 0))}</span><span class='hs-definition'>upperCaseString</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV &gt; 0)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x4:{VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),
                 (VV &gt;= 0),
                 (VV &lt; n),
                 (0 &lt;= VV)}
-&gt; {VV : (Int) | ((x4 = (x4 - 1)) =&gt; (VV = 0)),
                 ((x4 = (n - 1)) =&gt; (VV = 0)),
                 ((n = (x4 - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>s</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>n:{VV : (Int) | (VV &gt; 0)}
-&gt; i:{VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),
                   (VV &gt;= 0),
                   (VV &lt; n),
                   (0 &lt;= VV)}
-&gt; (x8:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                     ((n = (i - 1)) =&gt; (VV = 0)),
                     ((n = (n - 1)) =&gt; (VV = 0)),
                     (VV &gt;= 0),
                     (VV &lt; n),
                     (0 &lt;= VV)}
    -&gt; {VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                     ((x8 = (x8 - 1)) =&gt; (VV = 0)),
                     ((x8 = (n - 1)) =&gt; (VV = 0)),
                     ((n = (i - 1)) =&gt; (VV = 0)),
                     ((n = (x8 - 1)) =&gt; (VV = 0)),
                     ((n = (n - 1)) =&gt; (VV = 0))})
-&gt; x4:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                    ((n = (i - 1)) =&gt; (VV = 0)),
                    ((n = (n - 1)) =&gt; (VV = 0)),
                    (VV &gt;= 0),
                    (VV &lt; n)}
-&gt; {VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x4 = (x4 - 1)) =&gt; (VV = 0)),
                 ((x4 = (n - 1)) =&gt; (VV = 0)),
                 ((n = (i - 1)) =&gt; (VV = 0)),
                 ((n = (x4 - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>ucs</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = n),(VV &gt; 0)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>x4:{VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),
                 (VV &gt;= 0),
                 (VV &lt; n),
                 (0 &lt;= VV)}
-&gt; {VV : (Int) | ((x4 = (x4 - 1)) =&gt; (VV = 0)),
                 ((x4 = (n - 1)) =&gt; (VV = 0)),
                 ((n = (x4 - 1)) =&gt; (VV = 0)),
                 ((n = (n - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>s</span></a>
</pre>


Note that the length parameter `n` is provided solely as a ''witness'' for the length of the string `s`, which allows us to use the length of `s` in the type of `upperCaseString`; `n` is not used in the computation.

In order to establish that each call to `get` accesses string `s` within its bounds, our type system must establish that, at each call to the inner function `ucs`, `i` satisfies the type `{v: Int | 0 <= v && v < n}`.

This invariant is established as follows:

First, the invariant trivially holds on the first call to `ucs`, as
`n` is positive and `i` is `0`.
Second, we assume that `i` satisfies the type `{v: Int | 0 <= v && v < n}`, and, further, we know from the types of `s` and `get` that `c` has the type `{v: Int | i = n - 1 => c = 0}`.
Thus, if `c` is non-null, then `i` cannot be equal to `n - 1`.
This allows us to strengthen our type for `i` in the else branch to `{v: Int | 0 <= v && v < n - 1}` and thus to conclude that the value `i + 1` recursively passed as the `i` parameter to `ucs` satisfies the type `{v: Int | 0 <= v && v < n}`, establishing the inductive invariant and thus the safety of the `upperCaseString` function.



Memoization 
-----------

Next, let us illustrate how the same expressive signatures allow us to verify memoizing functions. We can specify to the SMT solver the definition of the Fibonacci function via an uninterpreted function `fib` and an axiom:


<pre><span class=hs-linenum>176: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>fib</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>177: </span>
<span class=hs-linenum>178: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>axiom_fib</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Bool</span> <span class='hs-keyword'>| (Prop(v) &lt;=&gt; 
                            (fib(i) = ((i &lt;= 1) ? 1 : ((fib(i-1)) + (fib(i-2))))))}</span> 
<span class=hs-linenum>180: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>181: </span><span class='hs-definition'>axiom_fib</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>182: </span><a class=annot href="#"><span class=annottext>i:(Int)
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (fib([i]) = ((i &lt;= 1) ? 1 : (fib([(i - 1)]) + fib([(i - 2)])))))}</span><span class='hs-definition'>axiom_fib</span></a> <a class=annot href="#"><span class=annottext>(Int)</span><span class='hs-varid'>i</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Bool) | false}</span><span class='hs-varid'>undefined</span></a>
</pre>

Next, we define a type alias `FibV` for the vector whose values are either `0` (ie undefined), or equal to the Fibonacci number of the corresponding index. 


<pre><span class=hs-linenum>188: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>FibV</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>j</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varid'>v</span> <span class='hs-varop'>!=</span> <span class='hs-num'>0</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>fib</span><span class='hs-layout'>(</span><span class='hs-varid'>j</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

Finally, we can use the above alias to verify `fastFib`, an implementation of the Fibonacci function, which uses an vector memoize intermediate results 


<pre><span class=hs-linenum>194: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fastFib</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = fib(x)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>195: </span><span class='hs-definition'>fastFib</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>196: </span><a class=annot href="#"><span class=annottext>x:(Int) -&gt; {VV : (Int) | (VV = fib([x]))}</span><span class='hs-definition'>fastFib</span></a> <a class=annot href="#"><span class=annottext>(Int)</span><span class='hs-varid'>n</span></a>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(({VV : (Int) | false}
  -&gt; {VV : (Int) | false}) , {VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),
                                           (VV = fib([n]))})
-&gt; {VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),(VV = fib([n]))}</span><span class='hs-varid'>snd</span></a> <a class=annot href="#"><span class=annottext>((({VV : (Int) | false}
   -&gt; {VV : (Int) | false}) , {VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),
                                            (VV = fib([n]))})
 -&gt; {VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),(VV = fib([n]))})
-&gt; (({VV : (Int) | false}
     -&gt; {VV : (Int) | false}) , {VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),
                                              (VV = fib([n]))})
-&gt; {VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0)),(VV = fib([n]))}</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>(j:(Int) -&gt; {VV : (Int) | ((VV != 0) =&gt; (VV = fib([j])))})
-&gt; i:(Int)
-&gt; (j:(Int)
    -&gt; {VV : (Int) | ((VV != 0) =&gt; (VV = fib([j])))} , {VV : (Int) | (VV = fib([i]))})</span><span class='hs-varid'>fibMemo</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Int) | ((n = (n - 1)) =&gt; (VV = 0))}
-&gt; {VV : (Int) | (VV = (0  :  int))}</span><span class='hs-keyglyph'>\</span></a><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = n)}</span><span class='hs-varid'>n</span></a>
<span class=hs-linenum>197: </span>
<span class=hs-linenum>198: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>fibMemo</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>FibV</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>FibV</span><span class='hs-layout'>,</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = fib(i)}</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>199: </span><a class=annot href="#"><span class=annottext>(x17:(Int)
 -&gt; {VV : (Int) | ((x17 = (x17 - 1)) =&gt; (VV = 0)),
                  ((VV != 0) =&gt; (VV = fib([x17])))})
-&gt; x14:(Int)
-&gt; (x9:{VV : (Int) | ((x14 = (x14 - 1)) =&gt; (VV = 0))}
    -&gt; {VV : (Int) | ((x14 = (x14 - 1)) =&gt; (VV = 0)),
                     ((x9 = (x9 - 1)) =&gt; (VV = 0)),
                     ((VV != 0) =&gt; (VV = fib([x9])))} , {VV : (Int) | ((x14 = (x14 - 1)) =&gt; (VV = 0)),
                                                                      (VV = fib([x14]))})</span><span class='hs-definition'>fibMemo</span></a> <a class=annot href="#"><span class=annottext>x3:(Int)
-&gt; {VV : (Int) | ((x3 = (x3 - 1)) =&gt; (VV = 0)),
                 ((VV != 0) =&gt; (VV = fib([x3])))}</span><span class='hs-varid'>t</span></a> <a class=annot href="#"><span class=annottext>(Int)</span><span class='hs-varid'>i</span></a> 
<span class=hs-linenum>200: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0))}
-&gt; y:{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0))}
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a>    
<span class=hs-linenum>201: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a -&gt; b -&gt; Bool&gt;.
x1:a -&gt; b&lt;p2 (fld, EVar x1) 1&gt; -&gt; (a , b)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>x3:(Int)
-&gt; {VV : (Int) | ((x3 = (x3 - 1)) =&gt; (VV = 0)),
                 ((VV != 0) =&gt; (VV = fib([x3])))}</span><span class='hs-varid'>t</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>b:(Bool)
-&gt; {VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 (VV = 1),
                 (VV &gt; 0),
                 (VV &gt;= i)}
-&gt; {VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
                 (? Prop([b])),
                 (VV = 1),
                 (VV &gt; 0),
                 (VV &gt;= i)}</span><span class='hs-varid'>liquidAssume</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>i:(Int)
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (fib([i]) = ((i &lt;= 1) ? 1 : (fib([(i - 1)]) + fib([(i - 2)])))))}</span><span class='hs-varid'>axiom_fib</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i)}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>202: </span>  
<span class=hs-linenum>203: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> 
<span class=hs-linenum>204: </span>  <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>case</span> <a class=annot href="#"><span class=annottext>forall &lt;r :: (Int) -&gt; (Int) -&gt; Bool , d :: (Int) -&gt; Bool&gt;.
i:(Int)&lt;d 0&gt;
-&gt; (j:(Int)&lt;d 0&gt;
    -&gt; {VV : (Int)&lt;r (x0, EVar j) 1&gt; | ((i = (i - 1)) =&gt; (VV = 0)),
                                       ((VV != 0) =&gt; (VV = fib([i])))})
-&gt; {VV : (Int)&lt;r (x0, EVar i) 1&gt; | ((i = (i - 1)) =&gt; (VV = 0)),
                                   ((VV != 0) =&gt; (VV = fib([i])))}</span><span class='hs-varid'>get</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x3:(Int)
-&gt; {VV : (Int) | ((x3 = (x3 - 1)) =&gt; (VV = 0)),
                 ((VV != 0) =&gt; (VV = fib([x3])))}</span><span class='hs-varid'>t</span></a> <span class='hs-keyword'>of</span>   
<span class=hs-linenum>205: </span>      <span class='hs-num'>0</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>let</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x3:{VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((i = (i - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0))}
-&gt; {VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x3 = (x3 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((VV != 0) =&gt; (VV = fib([x3])))}</span><span class='hs-varid'>t1</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
              ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((i = (i - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              (VV = n1)}</span><span class='hs-varid'>n1</span></a><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(x17:(Int)
 -&gt; {VV : (Int) | ((x17 = (x17 - 1)) =&gt; (VV = 0)),
                  ((VV != 0) =&gt; (VV = fib([x17])))})
-&gt; x14:(Int)
-&gt; (x9:{VV : (Int) | ((x14 = (x14 - 1)) =&gt; (VV = 0))}
    -&gt; {VV : (Int) | ((x14 = (x14 - 1)) =&gt; (VV = 0)),
                     ((x9 = (x9 - 1)) =&gt; (VV = 0)),
                     ((VV != 0) =&gt; (VV = fib([x9])))} , {VV : (Int) | ((x14 = (x14 - 1)) =&gt; (VV = 0)),
                                                                      (VV = fib([x14]))})</span><span class='hs-varid'>fibMemo</span></a> <a class=annot href="#"><span class=annottext>x3:(Int)
-&gt; {VV : (Int) | ((x3 = (x3 - 1)) =&gt; (VV = 0)),
                 ((VV != 0) =&gt; (VV = fib([x3])))}</span><span class='hs-varid'>t</span></a>  <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i)}</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x:(Int) -&gt; y:(Int) -&gt; {VV : (Int) | (VV = (x - y))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>206: </span>               <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x3:{VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((i = (i - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                 (VV != i)}
-&gt; {VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x3 = (x3 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                 ((VV != 0) =&gt; (VV = fib([x3])))}</span><span class='hs-varid'>t2</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
              ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((i = (i - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n2 = (n2 - 1)) =&gt; (VV = 0)),
              (VV = n2)}</span><span class='hs-varid'>n2</span></a><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(x17:(Int)
 -&gt; {VV : (Int) | ((x17 = (x17 - 1)) =&gt; (VV = 0)),
                  ((VV != 0) =&gt; (VV = fib([x17])))})
-&gt; x14:(Int)
-&gt; (x9:{VV : (Int) | ((x14 = (x14 - 1)) =&gt; (VV = 0))}
    -&gt; {VV : (Int) | ((x14 = (x14 - 1)) =&gt; (VV = 0)),
                     ((x9 = (x9 - 1)) =&gt; (VV = 0)),
                     ((VV != 0) =&gt; (VV = fib([x9])))} , {VV : (Int) | ((x14 = (x14 - 1)) =&gt; (VV = 0)),
                                                                      (VV = fib([x14]))})</span><span class='hs-varid'>fibMemo</span></a> <a class=annot href="#"><span class=annottext>x3:{VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((i = (i - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0))}
-&gt; {VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x3 = (x3 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((VV != 0) =&gt; (VV = fib([x3])))}</span><span class='hs-varid'>t1</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i)}</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x:(Int) -&gt; y:(Int) -&gt; {VV : (Int) | (VV = (x - y))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (2  :  int))}</span><span class='hs-num'>2</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>207: </span>               <a class=annot href="#"><span class=annottext>{VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
              ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((i = (i - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n2 = (n2 - 1)) =&gt; (VV = 0)),
              ((n2 = (n2 - 1)) =&gt; (VV = 0)),
              ((n2 = (n2 - 1)) =&gt; (VV = 0)),
              ((n2 = (n2 - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>n</span></a>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>b:(Bool)
-&gt; {VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((i = (i - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                 ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                 ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                 ((n2 = (n2 - 1)) =&gt; (VV = 0))}
-&gt; {VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((i = (i - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                 ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                 ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                 ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                 (? Prop([b]))}</span><span class='hs-varid'>liquidAssume</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>i:(Int)
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (fib([i]) = ((i &lt;= 1) ? 1 : (fib([(i - 1)]) + fib([(i - 2)])))))}</span><span class='hs-varid'>axiom_fib</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i)}</span><span class='hs-varid'>i</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
              ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((i = (i - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              (VV = n1),
              (VV = n1)}</span><span class='hs-varid'>n1</span></a> <a class=annot href="#"><span class=annottext>x:(Int) -&gt; y:(Int) -&gt; {VV : (Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
              ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((i = (i - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n2 = (n2 - 1)) =&gt; (VV = 0)),
              (VV = n2),
              (VV = n2)}</span><span class='hs-varid'>n2</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>208: </span>           <span class='hs-keyword'>in</span>  <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a -&gt; b -&gt; Bool&gt;.
x1:a -&gt; b&lt;p2 (fld, EVar x1) 1&gt; -&gt; (a , b)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>forall &lt;d :: (Int) -&gt; Bool , r :: (Int) -&gt; (Int) -&gt; Bool&gt;.
i:(Int)&lt;d 0&gt;
-&gt; {VV : (Int)&lt;r (x0,
                  EVar i) 1&gt; | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                               ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                               ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
                               ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                               ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                               ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
                               ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
                               ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
                               ((i = (i - 1)) =&gt; (VV = 0)),
                               ((n = (n - 1)) =&gt; (VV = 0)),
                               ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                               ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                               ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                               ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                               ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                               ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                               ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                               ((n2 = (n2 - 1)) =&gt; (VV = 0))}
-&gt; (j:{VV : (Int)&lt;d 0&gt; | (VV != i)}
    -&gt; {VV : (Int)&lt;r (x0,
                      EVar j) 1&gt; | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                                   ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                                   ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
                                   ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                                   ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                                   ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
                                   ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
                                   ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
                                   ((i = (i - 1)) =&gt; (VV = 0)),
                                   ((n = (n - 1)) =&gt; (VV = 0)),
                                   ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                                   ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                                   ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                                   ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                                   ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                                   ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                                   ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                                   ((n2 = (n2 - 1)) =&gt; (VV = 0))})
-&gt; k:(Int)&lt;d 0&gt;
-&gt; {VV : (Int)&lt;r (x0,
                  EVar k) 1&gt; | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                               ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                               ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
                               ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                               ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                               ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
                               ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
                               ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
                               ((i = (i - 1)) =&gt; (VV = 0)),
                               ((n = (n - 1)) =&gt; (VV = 0)),
                               ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                               ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                               ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                               ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                               ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                               ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                               ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                               ((n2 = (n2 - 1)) =&gt; (VV = 0))}</span><span class='hs-varid'>set</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = i)}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
              ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((i = (i - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n2 = (n2 - 1)) =&gt; (VV = 0)),
              ((n2 = (n2 - 1)) =&gt; (VV = 0)),
              ((n2 = (n2 - 1)) =&gt; (VV = 0)),
              ((n2 = (n2 - 1)) =&gt; (VV = 0)),
              (VV = n)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x3:{VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((i = (i - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                 (VV != i)}
-&gt; {VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
                 ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
                 ((i = (i - 1)) =&gt; (VV = 0)),
                 ((x3 = (x3 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n1 = (n1 - 1)) =&gt; (VV = 0)),
                 ((n2 = (n2 - 1)) =&gt; (VV = 0)),
                 ((VV != 0) =&gt; (VV = fib([x3])))}</span><span class='hs-varid'>t2</span></a><span class='hs-layout'>,</span>  <a class=annot href="#"><span class=annottext>{VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((ds_dCS = (i - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((ds_dCT = (i - 1)) =&gt; (VV = 0)),
              ((i = (ds_dCS - 1)) =&gt; (VV = 0)),
              ((i = (ds_dCT - 1)) =&gt; (VV = 0)),
              ((i = (i - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n1 = (n1 - 1)) =&gt; (VV = 0)),
              ((n2 = (n2 - 1)) =&gt; (VV = 0)),
              ((n2 = (n2 - 1)) =&gt; (VV = 0)),
              ((n2 = (n2 - 1)) =&gt; (VV = 0)),
              ((n2 = (n2 - 1)) =&gt; (VV = 0)),
              (VV = n)}</span><span class='hs-varid'>n</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>209: </span>      <span class='hs-varid'>n</span> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>(x4:{VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                  ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                  ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                  ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                  ((i = (i - 1)) =&gt; (VV = 0))}
 -&gt; {VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                  ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                  ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                  ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                  ((i = (i - 1)) =&gt; (VV = 0)),
                  ((x4 = (x4 - 1)) =&gt; (VV = 0)),
                  ((VV != 0) =&gt; (VV = fib([x4])))} , {VV : (Int) | ((ds_dCS = (ds_dCS - 1)) =&gt; (VV = 0)),
                                                                   ((ds_dCS = (ds_dCT - 1)) =&gt; (VV = 0)),
                                                                   ((ds_dCT = (ds_dCS - 1)) =&gt; (VV = 0)),
                                                                   ((ds_dCT = (ds_dCT - 1)) =&gt; (VV = 0)),
                                                                   ((i = (i - 1)) =&gt; (VV = 0)),
                                                                   (VV = ds_dCS),
                                                                   (VV = ds_dCT),
                                                                   (VV = fib([i])),
                                                                   (VV != 0)})</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>x3:(Int)
-&gt; {VV : (Int) | ((x3 = (x3 - 1)) =&gt; (VV = 0)),
                 ((VV != 0) =&gt; (VV = fib([x3])))}</span><span class='hs-varid'>t</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | ((i = (i - 1)) =&gt; (VV = 0)),
              ((VV != 0) =&gt; (VV = fib([i]))),
              (VV = ds_dCS)}</span><span class='hs-varid'>n</span></a><span class='hs-layout'>)</span>
</pre>

Thus, abstract refinements allow us to define key-value maps with index-dependent refinements for the domain and range. 
Quantification over the domain and range refinements allows us to define generic access operations (eg. `get`, `set`, `create`, `empty`) whose types enable us establish a variety of precise invariants.




