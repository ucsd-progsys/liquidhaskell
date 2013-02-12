---
layout: post
title: "Verifing Sorting Algorithms With Recursive Refinements"
date: 2013-01-25 16:12
comments: true
external-url:
categories: abstract-refinements
author: Niki Vazou
published: false
---

Let see how we can use **abstract refinements* to verify that
the result of a list sorting function is actually a sorted list.


<pre><span class=hs-linenum>16: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>ListSort</span> <span class='hs-layout'>(</span><span class='hs-varid'>insertSort</span><span class='hs-layout'>,</span> <span class='hs-varid'>mergeSort</span><span class='hs-layout'>,</span> <span class='hs-varid'>quickSort</span><span class='hs-layout'>)</span> <span class='hs-keyword'>where</span>
</pre>

First, lets describe a sorted list:

The list type is refined with an abstract refinement, yielding the refined type:
<pre><span class=hs-linenum>22: </span><span class='hs-keyword'>data</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>elt</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>23: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-conid'>[]</span>  <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span>
<span class=hs-linenum>24: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conop'>:</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>h</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>h</span><span class='hs-varop'>&gt;</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span>
</pre>

The definition states that a value of type `[a]<p>` is either empty (`[]`)
or constructed from a pair of a head `h::a` and a tail of a list of a values 
each of which satisfies the refinement (`p h`). 
Furthermore, the abstract refinement `p` holds recursively within the
tail, ensuring that the relationship `p` holds between all pairs of list elements.


A sorted list is defined by instantiating the abstract refinement `p` with 
<pre><span class=hs-linenum>35: </span><span class='hs-keyglyph'>\</span><span class='hs-varid'>elt</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>elt</span>
</pre>

So, we define the type-synonym `SList a`


<pre><span class=hs-linenum>41: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>SList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;\</span><span class='hs-varid'>elt</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>v</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>elt</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>@-}</span>
</pre>

We aim to verify that the result of each sorting function is of type `SList a`

Insert Sort
-----------

Lets write a function `insert` that inserts an element into the correct position of a sorted list:


<pre><span class=hs-linenum>52: </span><a class=annot href="#"><span class=annottext>a -&gt; {VV : [a] | (len([VV]) &gt;= 0)} -&gt; {VV : [a] | (len([VV]) &gt; 0)}</span><span class='hs-definition'>insert</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>y</span></a> <span class='hs-conid'>[]</span>                   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}] | (len([VV]) = 0),(len([VV]) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>53: </span><span class='hs-definition'>insert</span> <span class='hs-varid'>y</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span> <span class='hs-conop'>:</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:{VV : a | (VV &gt;= y)}
-&gt; ys:[{VV : a&lt;p (fld, EVar y) 1&gt; | (VV &gt;= y)}]
-&gt; {VV : [{VV : a | (VV &gt;= y)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:{VV : a | (VV &gt;= x),(VV &gt;= y)}
-&gt; ys:[{VV : a&lt;p (fld, EVar y) 1&gt; | (VV &gt;= x),(VV &gt;= y)}]
-&gt; {VV : [{VV : a | (VV &gt;= x),
                    (VV &gt;= y)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= x)}] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> 
<span class=hs-linenum>54: </span>                  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:{VV : a | (VV &gt;= x)}
-&gt; ys:[{VV : a&lt;p (fld, EVar y) 1&gt; | (VV &gt;= x)}]
-&gt; {VV : [{VV : a | (VV &gt;= x)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>a -&gt; {VV : [a] | (len([VV]) &gt;= 0)} -&gt; {VV : [a] | (len([VV]) &gt; 0)}</span><span class='hs-varid'>insert</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= x)}] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

Its type states that if you give `insert` an element and a sorted list,
it returns a sorted list.
 
To write `insertSort`, 
we can recursively apply this `insert` to the elements of the list:


<pre><span class=hs-linenum>64: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>insertSort</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>SList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>65: </span><span class='hs-definition'>insertSort</span>            <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>66: </span><a class=annot href="#"><span class=annottext>forall a. (Ord a) -&gt; [a] -&gt; [a]</span><span class='hs-definition'>insertSort</span></a> <span class='hs-conid'>[]</span>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
{VV : [{VV : a | false}] | (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>67: </span><span class='hs-definition'>insertSort</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a -&gt; {VV : [a] | (len([VV]) &gt;= 0)} -&gt; {VV : [a] | (len([VV]) &gt; 0)}</span><span class='hs-varid'>insert</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>[a] -&gt; [a]</span><span class='hs-varid'>insertSort</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span> 
</pre>

And the system can prove that the result of `insertSort` is a sorted list.

Merge Sort
----------

We first write a `merge` function:


<pre><span class=hs-linenum>78: </span><span class='hs-definition'>merge</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>79: </span><a class=annot href="#"><span class=annottext>forall a.
(Ord a)
-&gt; {VV : [a] | (len([VV]) &gt;= 0)}
-&gt; {VV : [a] | (len([VV]) &gt;= 0)}
-&gt; {VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-definition'>merge</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <span class='hs-conid'>[]</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>80: </span><span class='hs-definition'>merge</span> <span class='hs-conid'>[]</span> <span class='hs-varid'>ys</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ds_dK5),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
<span class=hs-linenum>81: </span><span class='hs-definition'>merge</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>ys</span><span class='hs-layout'>)</span>
<span class=hs-linenum>82: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a>
<span class=hs-linenum>83: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:{VV : a | (VV &gt;= x)}
-&gt; ys:[{VV : a&lt;p (fld, EVar y) 1&gt; | (VV &gt;= x)}]
-&gt; {VV : [{VV : a | (VV &gt;= x)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a><span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a.
(Ord a)
-&gt; {VV : [a] | (len([VV]) &gt;= 0)}
-&gt; {VV : [a] | (len([VV]) &gt;= 0)}
-&gt; {VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>merge</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= x)}] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:{VV : a | (VV &gt;= x),(VV &gt;= y)}
-&gt; ys:[{VV : a&lt;p (fld, EVar y) 1&gt; | (VV &gt;= x),(VV &gt;= y)}]
-&gt; {VV : [{VV : a | (VV &gt;= x),
                    (VV &gt;= y)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= y)}] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>84: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> 
<span class=hs-linenum>85: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:{VV : a | (VV &gt;= y)}
-&gt; ys:[{VV : a&lt;p (fld, EVar y) 1&gt; | (VV &gt;= y)}]
-&gt; {VV : [{VV : a | (VV &gt;= y)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a><span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall a.
(Ord a)
-&gt; {VV : [a] | (len([VV]) &gt;= 0)}
-&gt; {VV : [a] | (len([VV]) &gt;= 0)}
-&gt; {VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>merge</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:{VV : a | (VV &gt; y),(VV &gt;= x)}
-&gt; ys:[{VV : a&lt;p (fld, EVar y) 1&gt; | (VV &gt; y),(VV &gt;= x)}]
-&gt; {VV : [{VV : a | (VV &gt; y),
                    (VV &gt;= x)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= x)}] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= y)}] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span>
</pre>

The system can prove that if both arguments of `merge` are sorted lists, 
then its result is also a sorted list.

Next, we write a `split` function that splits any list in two sublists:

<pre><span class=hs-linenum>93: </span><span class='hs-definition'>split</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-layout'>,</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-layout'>)</span>
<span class=hs-linenum>94: </span><a class=annot href="#"><span class=annottext>forall a.
{VV : [a] | (len([VV]) &gt;= 0)}
-&gt; ({VV : [a] | (len([VV]) &gt;= 0)} , {VV : [a] | (len([VV]) &gt;= 0)})</span><span class='hs-definition'>split</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>zs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a -&gt; b -&gt; Bool&gt;.
x1:a -&gt; b&lt;p2 (fld, EVar x1) 1&gt; -&gt; (a , b)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p (fld, EVar y) 1&gt;]
-&gt; {VV : [a] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),
            (VV = xs),
            (len([VV]) = len([xs])),
            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p (fld, EVar y) 1&gt;]
-&gt; {VV : [a] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),
            (VV = ys),
            (len([VV]) = len([ys])),
            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span> <span class='hs-keyword'>where</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) = len([xs])),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) = len([ys])),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
{VV : [a] | (len([VV]) &gt;= 0)}
-&gt; ({VV : [a] | (len([VV]) &gt;= 0)} , {VV : [a] | (len([VV]) &gt;= 0)})</span><span class='hs-varid'>split</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = zs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>zs</span></a>
<span class=hs-linenum>95: </span><span class='hs-definition'>split</span> <span class='hs-varid'>xs</span>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a b &lt;p2 :: a -&gt; b -&gt; Bool&gt;.
x1:a -&gt; b&lt;p2 (fld, EVar x1) 1&gt; -&gt; (a , b)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ds_dJS),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}] | (len([VV]) = 0),(len([VV]) &gt;= 0)}</span><span class='hs-conid'>[]</span></a><span class='hs-layout'>)</span>
</pre>

Finally, using the above functions we write `mergeSort`:


<pre><span class=hs-linenum>101: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>mergeSort</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>SList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>102: </span><span class='hs-definition'>mergeSort</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>103: </span><a class=annot href="#"><span class=annottext>forall a. (Ord a) -&gt; [a] -&gt; [a]</span><span class='hs-definition'>mergeSort</span></a> <span class='hs-conid'>[]</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
{VV : [{VV : a | false}] | (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>104: </span><span class='hs-definition'>mergeSort</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}] | (len([VV]) = 0),(len([VV]) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>105: </span><span class='hs-definition'>mergeSort</span> <span class='hs-varid'>xs</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
(Ord a)
-&gt; {VV : [a] | (len([VV]) &gt;= 0)}
-&gt; {VV : [a] | (len([VV]) &gt;= 0)}
-&gt; {VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>merge</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>[a] -&gt; [a]</span><span class='hs-varid'>mergeSort</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs1),
            (VV = xs1),
            (len([VV]) = len([xs1])),
            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs1</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>[a] -&gt; [a]</span><span class='hs-varid'>mergeSort</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs2),
            (VV = xs2),
            (len([VV]) = len([xs2])),
            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs2</span></a><span class='hs-layout'>)</span> <span class='hs-keyword'>where</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs1),(len([VV]) = len([xs1])),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs1</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs2),(len([VV]) = len([xs2])),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs2</span></a><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
{VV : [a] | (len([VV]) &gt;= 0)}
-&gt; ({VV : [a] | (len([VV]) &gt;= 0)} , {VV : [a] | (len([VV]) &gt;= 0)})</span><span class='hs-varid'>split</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ds_dKg),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

The system can prove that the result of `mergeSort` is a sorted list.
For the first two cases empty lists or lists with one element can easily proved
to be sorted. For the last case, if we assume that `mergeSort`'s result is a 
sorted list, then `merge` is applied to two sorted lists, thus its result will
be also a sorted list.

Quick Sort
----------

We would like to define `quickSort` as follows:
<pre><span class=hs-linenum>118: </span><span class='hs-definition'>quickSort'</span> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <span class='hs-conid'>[]</span>
<span class=hs-linenum>119: </span><span class='hs-definition'>quickSort'</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>append'</span> <span class='hs-varid'>lts</span> <span class='hs-varid'>gts</span> 
<span class=hs-linenum>120: </span>  <span class='hs-keyword'>where</span> <span class='hs-varid'>lts</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>quickSort'</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>y</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>y</span> <span class='hs-keyglyph'>&lt;-</span> <span class='hs-varid'>xs</span><span class='hs-layout'>,</span> <span class='hs-varid'>y</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>121: </span>        <span class='hs-varid'>gts</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>quickSort'</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>z</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>z</span> <span class='hs-keyglyph'>&lt;-</span> <span class='hs-varid'>xs</span><span class='hs-layout'>,</span> <span class='hs-varid'>z</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>x</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>122: </span>
<span class=hs-linenum>123: </span><span class='hs-definition'>append'</span> <span class='hs-conid'>[]</span>     <span class='hs-varid'>ys</span>  <span class='hs-keyglyph'>=</span> <span class='hs-varid'>ys</span>
<span class=hs-linenum>124: </span><span class='hs-definition'>append'</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varid'>ys</span>  <span class='hs-keyglyph'>=</span> <span class='hs-varid'>x</span> <span class='hs-conop'>:</span> <span class='hs-varid'>append'</span> <span class='hs-varid'>xs</span> <span class='hs-varid'>ys</span>
</pre>


In order for `quicksort` to return a sorted list,
append should return a sorted list.
Thus, we would like to be able to express the fact that `append`
is called with two sorted lists and each element of the first list 
is less than each element of the second.
To do so, we provide `append` one more argument or a "ghost" variable, say `k`, of type `a`
and give it the type


<pre><span class=hs-linenum>137: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>append</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>k</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>l</span><span class='hs-conop'>:</span><span class='hs-conid'>SList</span> <span class='hs-keyword'>{v:</span><span class='hs-definition'>a</span> <span class='hs-keyword'>| v&lt;k}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ge</span><span class='hs-conop'>:</span><span class='hs-conid'>SList</span> <span class='hs-keyword'>{v:</span><span class='hs-definition'>a</span> <span class='hs-keyword'>| v&gt;=k}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>SList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
</pre>

So, `append` is defined as:


<pre><span class=hs-linenum>143: </span><span class='hs-definition'>append</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>144: </span><a class=annot href="#"><span class=annottext>forall a.
k:a -&gt; [{VV : a | (VV &lt; k)}] -&gt; [{VV : a | (VV &gt;= k)}] -&gt; [a]</span><span class='hs-definition'>append</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>k</span></a> <span class='hs-conid'>[]</span>     <a class=annot href="#"><span class=annottext>[{VV : a | (VV &gt;= k)}]</span><span class='hs-varid'>ys</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= k)}] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
<span class=hs-linenum>145: </span><span class='hs-definition'>append</span> <span class='hs-varid'>k</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varid'>ys</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x),(VV &lt; k)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:{VV : a | (VV &gt;= x)}
-&gt; ys:[{VV : a&lt;p (fld, EVar y) 1&gt; | (VV &gt;= x)}]
-&gt; {VV : [{VV : a | (VV &gt;= x)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>k:{VV : a | (VV &gt;= x)}
-&gt; [{VV : a | (VV &gt;= x),(VV &lt; k)}]
-&gt; [{VV : a | (VV &gt;= k),(VV &gt;= x)}]
-&gt; [{VV : a | (VV &gt;= x)}]</span><span class='hs-varid'>append</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = k)}</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= x),(VV &lt; k)}] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= k)}] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
</pre>

And finally we can define `quicksort`:


<pre><span class=hs-linenum>151: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>quickSort</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>SList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>152: </span><a class=annot href="#"><span class=annottext>[a] -&gt; [a]</span><span class='hs-definition'>quickSort</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
{VV : [{VV : a | false}] | (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>153: </span><span class='hs-definition'>quickSort</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>k:a -&gt; [{VV : a | (VV &lt; k)}] -&gt; [{VV : a | (VV &gt;= k)}] -&gt; [a]</span><span class='hs-varid'>append</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &lt; x)}] | (VV = lts),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>lts</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= x)}] | (VV = gts),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>gts</span></a> 
<span class=hs-linenum>154: </span>  <span class='hs-keyword'>where</span> <a class=annot href="#"><span class=annottext>[{VV : a | (VV &lt; x)}]</span><span class='hs-varid'>lts</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[a] -&gt; [a]</span><span class='hs-varid'>quickSort</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &lt; x)}] | (len([VV]) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV = ds_dJL)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>y</span> <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = ds_dJL)}</span><span class='hs-varid'>y</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt; y))}</span><span class='hs-varop'>&lt;</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>155: </span>        <a class=annot href="#"><span class=annottext>[{VV : a | (VV &gt;= x)}]</span><span class='hs-varid'>gts</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[a] -&gt; [a]</span><span class='hs-varid'>quickSort</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (VV &gt;= x)}] | (len([VV]) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : a | (VV = ds_dJP)}</span><span class='hs-varid'>z</span></a> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>z</span> <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = ds_dJP)}</span><span class='hs-varid'>z</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; y:a -&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x &gt;= y))}</span><span class='hs-varop'>&gt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span>
</pre>

