
---
layout: post
title: "Reasoning about Sets of Values"
date: 2013-01-05 16:12
comments: true
external-url:
categories: basic, measures, sets
author: Ranjit Jhala
published: false 
---

SMT solvers support very expressive logics. Lets see how we can represent the *set of*
elements in a list, and then write and verify precise specifications about
those sets.


<pre><span class=hs-linenum>18: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>ListSets</span> <span class='hs-keyword'>where</span>
</pre>

First, lets import the type `Set a` that represents sets


<pre><span class=hs-linenum>24: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> 
</pre>

Next, lets write a measure for the set of elements in a list.
The measure is a simple recursive function that computes the set
by structural recursion on the list.

 A measure for the elements of a list
<pre><span class=hs-linenum>32: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>elts</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>33: </span>    <span class='hs-varid'>elts</span> <span class='hs-layout'>(</span><span class='hs-conid'>[]</span><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>{v | (? Set_emp(v))}
    elts (x:</span><span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cup</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>elts</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-layout'>}</span>
<span class=hs-linenum>35: </span>  <span class='hs-keyword'>@-}</span>
</pre>

 we tell the solver to interpret `Set` *natively* in the refinement logic, via the solver's built in sort.
<pre><span class=hs-linenum>39: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>embed</span> <span class='hs-conid'>Set</span> <span class='hs-keyword'>as</span> <span class='hs-conid'>Set_Set</span> <span class='hs-keyword'>@-}</span>
</pre>

OK, now we can write some specifications!

A Trivial Identity
------------------

To start with, lets check that the `elts` measure is sensible.


<pre><span class=hs-linenum>50: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>myid</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-keyword'>| (elts v) = (elts xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>51: </span><a class=annot href="#"><span class=annottext>x4:[a]
-&gt; {VV : [a] | (elts([VV]) = Set_cup([elts([x4]); elts([x4])])),
               (elts([VV]) = elts([x4])),
               (len([VV]) = len([x4])),
               (len([VV]) &gt;= 0)}</span><span class='hs-definition'>myid</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
{VV : [{VV : a | false}] | (? Set_emp([elts([VV])])),
                           (? Set_emp([listElts([VV])])),
                           (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>52: </span><span class='hs-definition'>myid</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p (fld, EVar y) 1&gt;]
-&gt; {VV : [a] | (elts([VV]) = Set_cup([Set_sng([y]); elts([ys])])),
               (len([VV]) = (1 + len([ys]))),
               (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>x4:[a]
-&gt; {VV : [a] | (elts([VV]) = Set_cup([elts([x4]); elts([x4])])),
               (elts([VV]) = elts([x4])),
               (len([VV]) = len([x4])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>myid</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

A Less Trivial Identity
-----------------------

Next, lets write a function `myreverse` that reverses a list. 
Of course, it should also preserve the set of values thats in 
the list. This is somewhat more interesting because of the 
*tail recursive* helper `go`. Mouse over and see what type 
is inferred for it!


<pre><span class=hs-linenum>65: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>myreverse</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-keyword'>| (elts v) = (elts xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>66: </span><a class=annot href="#"><span class=annottext>forall a. xs:[a] -&gt; {VV : [a] | (elts([VV]) = elts([xs]))}</span><span class='hs-definition'>myreverse</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x4:{VV : [{VV : a | false}] | (len([VV]) = 0)}
-&gt; x3:[a]
-&gt; {VV : [a] | (elts([VV]) = Set_cup([elts([x4]); elts([x3])])),
               (elts([VV]) = Set_cup([elts([x3]); elts([x4])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}] | (? Set_emp([elts([VV])])),
                           (? Set_emp([listElts([VV])])),
                           (len([VV]) = 0),
                           (len([VV]) &gt;= 0)}</span><span class='hs-conid'>[]</span></a> 
<span class=hs-linenum>67: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>68: </span>    <a class=annot href="#"><span class=annottext>acc:{VV : [a] | (len([VV]) &gt;= 0)}
-&gt; ds_dhQ:[a]
-&gt; {VV : [a] | (elts([VV]) = Set_cup([elts([acc]);
                                      elts([ds_dhQ])])),
               (elts([VV]) = Set_cup([elts([ds_dhQ]); elts([acc])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>acc</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = acc),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>acc</span></a>
<span class=hs-linenum>69: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>acc</span> <span class='hs-layout'>(</span><span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>ys</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>acc:{VV : [a] | (len([VV]) &gt;= 0)}
-&gt; ds_dhQ:[a]
-&gt; {VV : [a] | (elts([VV]) = Set_cup([elts([acc]);
                                      elts([ds_dhQ])])),
               (elts([VV]) = Set_cup([elts([ds_dhQ]); elts([acc])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>go</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p (fld, EVar y) 1&gt;]
-&gt; {VV : [a] | (elts([VV]) = Set_cup([Set_sng([y]); elts([ys])])),
               (len([VV]) = (1 + len([ys]))),
               (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = acc),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>acc</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
</pre>

Appending Lists
---------------

Next, here's good old append, but now with a specification that states
that the output indeed includes the elements from both the input lists.


<pre><span class=hs-linenum>79: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>myapp</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>| (elts v) = (Set_cup (elts xs) (elts ys))}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>80: </span><a class=annot href="#"><span class=annottext>x4:[a]
-&gt; x3:[a]
-&gt; {VV : [a] | (elts([VV]) = Set_cup([elts([x4]); elts([x3])])),
               (elts([VV]) = Set_cup([elts([x3]); elts([x4])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-definition'>myapp</span></a> <span class='hs-conid'>[]</span>     <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>ys</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
<span class=hs-linenum>81: </span><span class='hs-definition'>myapp</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varid'>ys</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p (fld, EVar y) 1&gt;]
-&gt; {VV : [a] | (elts([VV]) = Set_cup([Set_sng([y]); elts([ys])])),
               (len([VV]) = (1 + len([ys]))),
               (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>x4:[a]
-&gt; x3:[a]
-&gt; {VV : [a] | (elts([VV]) = Set_cup([elts([x4]); elts([x3])])),
               (elts([VV]) = Set_cup([elts([x3]); elts([x4])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>myapp</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
</pre>

Filtering Lists
---------------

Finally, to round off this little demo, here's `filter`. We can verify
that it returns a subset of the values of the input list.


<pre><span class=hs-linenum>91: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>myfilter</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-keyword'>| (? (Set_sub (elts v) (elts xs)))}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>92: </span><a class=annot href="#"><span class=annottext>(a -&gt; (Bool))
-&gt; x1:[a]
-&gt; {VV : [a] | (? Set_sub([elts([VV]); elts([x1])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-definition'>myfilter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (Bool)</span><span class='hs-varid'>f</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
{VV : [{VV : a | false}] | (? Set_emp([elts([VV])])),
                           (? Set_emp([listElts([VV])])),
                           (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>93: </span><span class='hs-definition'>myfilter</span> <span class='hs-varid'>f</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>94: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>a -&gt; (Bool)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a>           <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a -&gt; a -&gt; Bool&gt;.
y:a
-&gt; ys:[a&lt;p (fld, EVar y) 1&gt;]
-&gt; {VV : [a] | (elts([VV]) = Set_cup([Set_sng([y]); elts([ys])])),
               (len([VV]) = (1 + len([ys]))),
               (listElts([VV]) = Set_cup([Set_sng([y]); listElts([ys])]))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>(a -&gt; (Bool))
-&gt; x1:[a]
-&gt; {VV : [a] | (? Set_sub([elts([VV]); elts([x1])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>myfilter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (Bool)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> 
<span class=hs-linenum>95: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(a -&gt; (Bool))
-&gt; x1:[a]
-&gt; {VV : [a] | (? Set_sub([elts([VV]); elts([x1])])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>myfilter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (Bool)</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>



