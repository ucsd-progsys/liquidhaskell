---
layout: post
title: Unique Zippers
date: 2013-05-10 16:12
comments: true
tags: basic, measures, sets, uniqueness
author: Niki Vazou
published: true
demo: UniqueZipper.hs
---

**The story so far:** [Previously][about-sets] we saw
how we can use LiquidHaskell to talk about set of values
and specifically the *set of values* in a list.

Often, we want to enforce the invariant that a particular data structure
contains *no duplicates*. For example, we may have a structure that holds
a collection of file handles, or other resources, where the presence of
duplicates could lead to unpleasant leaks.

In this post, we will see how to use LiquidHaskell to talk
about the set of duplicate values in data structures, and 
hence, let us specify and verify uniqueness, that is, the
absence of duplicates.

<!-- more -->

To begin, lets extend our vocabulary to talk about the *set of duplicate
values* in lists.  By constraining this set to be empty, we can specify a
list without duplicates, or an **unique list**.  Once we express uniqueness
on lists, it is straightforward to describe uniqueness on other data
structures that contain lists.  As an example, we will illustrate the
properties of a **unique zipper**.


<pre><span class=hs-linenum>37: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>UniqueZipper</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>38: </span>
<span class=hs-linenum>39: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span>  <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>reverse</span><span class='hs-layout'>,</span> <span class='hs-layout'>(</span><span class='hs-varop'>++</span><span class='hs-layout'>)</span><span class='hs-layout'>,</span> <span class='hs-varid'>filter</span><span class='hs-layout'>)</span>
<span class=hs-linenum>40: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>filter</span><span class='hs-layout'>)</span>
</pre>


A Quick Recap
=============

 In the previous post we used a measure for the elements of a list, from [Data/Set.spec][setspec]
<pre><span class=hs-linenum>48: </span><span class='hs-definition'>measure</span> <span class='hs-varid'>listElts</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>49: </span><span class='hs-definition'>listElts</span> <span class='hs-layout'>(</span><span class='hs-conid'>[]</span><span class='hs-layout'>)</span>    <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varop'>?</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_emp</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>50: </span><span class='hs-definition'>listElts</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span>  <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cup</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-layout'>}</span>
</pre>

With this measure we defined predicate aliases 
that describe relations between lists:


<pre><span class=hs-linenum>57: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>EqElts</span>  <span class='hs-conid'>X</span> <span class='hs-conid'>Y</span>      <span class='hs-keyglyph'>=</span> 
<span class=hs-linenum>58: </span>      <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>Y</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>                        <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>59: </span>
<span class=hs-linenum>60: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>DisjointElts</span> <span class='hs-conid'>X</span> <span class='hs-conid'>Y</span> <span class='hs-keyglyph'>=</span> 
<span class=hs-linenum>61: </span>      <span class='hs-layout'>(</span><span class='hs-conid'>Set_emp</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cap</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>Y</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>        <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>62: </span>
<span class=hs-linenum>63: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>SubElts</span> <span class='hs-conid'>X</span> <span class='hs-conid'>Y</span>      <span class='hs-keyglyph'>=</span> 
<span class=hs-linenum>64: </span>      <span class='hs-layout'>(</span><span class='hs-conid'>Set_sub</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>Y</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>                  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>65: </span>
<span class=hs-linenum>66: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>UnionElts</span> <span class='hs-conid'>X</span> <span class='hs-conid'>Y</span> <span class='hs-conid'>Z</span>  <span class='hs-keyglyph'>=</span> 
<span class=hs-linenum>67: </span>      <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cup</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>Y</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>Z</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>68: </span>
<span class=hs-linenum>69: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>ListElt</span> <span class='hs-conid'>N</span> <span class='hs-conid'>X</span>      <span class='hs-keyglyph'>=</span> 
<span class=hs-linenum>70: </span>      <span class='hs-layout'>(</span><span class='hs-conid'>Set_mem</span> <span class='hs-conid'>N</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>                             <span class='hs-keyword'>@-}</span>
</pre>


These predicates were our vocabulary on specifying properties of list functions.
Remember, that `reverse` returns an output list that has the same elements, i.e., `EqElts`, with the input list.
We can extend these predicates and express list uniqueness.
So reversing a unique list should again return an output list that has the same
elements as the input list, and also it is unique.

Describing Unique Lists
======================

To describe unique lists, we follow two steps:

1. we describe the set of duplicate values of a list; and 
2. we demand this set to be empty.

Towards the first step, we define a measure `dups`
that returns the duplicate values of its input list.
This measure is recursively defined:
The duplicates of an empty list is the empty set.
We compute the duplicates of a non-empty list, 
namely `x:xs`, as follows:

- If `x` is an element of `xs`, then `x` is a duplicate.
  Hence, `dups` is `x` plus the (recursively computed) 
  duplicates in `xs`.

- Otherwise, we can ignore `x` and recursively compute 
  the duplicates of `xs`.

The above intuition can be formalized as a measure:


<pre><span class=hs-linenum>105: </span><span class='hs-keyword'>{-@</span>
<span class=hs-linenum>106: </span>  <span class='hs-varid'>measure</span> <span class='hs-varid'>dups</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>107: </span>  <span class='hs-varid'>dups</span><span class='hs-layout'>(</span><span class='hs-conid'>[]</span><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varop'>?</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_emp</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
<span class=hs-linenum>108: </span>  <span class='hs-varid'>dups</span><span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-keyword'>if</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_mem</span> <span class='hs-varid'>x</span> <span class='hs-layout'>(</span><span class='hs-varid'>listElts</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>109: </span>                         <span class='hs-keyword'>then</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_cup</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_sng</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>dups</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>110: </span>                         <span class='hs-keyword'>else</span> <span class='hs-layout'>(</span><span class='hs-varid'>dups</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-layout'>}</span>
<span class=hs-linenum>111: </span>  <span class='hs-keyword'>@-}</span>
</pre>

With `dups` in hand, it is direct to describe unique lists:

A list is unique, if the set of duplicates, as computed by `dups` is empty.

We create a type alias for unique lists and name it `UList`.


<pre><span class=hs-linenum>121: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>predicate</span> <span class='hs-conid'>ListUnique</span> <span class='hs-conid'>X</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>Set_emp</span> <span class='hs-layout'>(</span><span class='hs-varid'>dups</span> <span class='hs-conid'>X</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>122: </span>
<span class=hs-linenum>123: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>UList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conid'>ListUnique</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>     <span class='hs-keyword'>@-}</span>
</pre>


Functions on Unique Lists
==========================

In the previous post, we proved interesting properties about 
the list trilogy, i.e., `append`, `reverse`, and `filter`.
Now, we will prove that apart from these properties,
all these functions preserve list uniqueness.

Append
------

To begin with, we proved that the output of append
indeed includes the elements from both the input lists.
Now, we can also prove that if both input lists are 
unique *and their elements are disjoint*, then the 
output list is also unique.


<pre><span class=hs-linenum>145: </span><span class='hs-keyword'>infixr</span> <span class='hs-num'>5</span> <span class='hs-varop'>++</span>
<span class=hs-linenum>146: </span><span class='hs-keyword'>{-@</span> <span class='hs-layout'>(</span><span class='hs-varop'>++</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>UList</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>147: </span>         <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span><span class='hs-keyword'>{v:</span> <span class='hs-conid'>UList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>| (DisjointElts v xs)}</span>
<span class=hs-linenum>148: </span>         <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>UList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>| (UnionElts v xs ys)}</span>
<span class=hs-linenum>149: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>150: </span><span class='hs-layout'>(</span><span class='hs-varop'>++</span><span class='hs-layout'>)</span>         <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>151: </span><span class='hs-conid'>[]</span> <a class=annot href="#"><span class=annottext>forall a.
xs:{VV : [a] | ((Set_emp (dups VV)))}
-&gt; ys:{VV : [a] | ((Set_emp (Set_cap (listElts VV) (listElts xs)))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((listElts VV) == (Set_cup (listElts xs) (listElts ys)))}</span><span class='hs-varop'>++</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | ((Set_emp (dups VV)))}</span><span class='hs-varid'>ys</span></a>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | ((Set_emp (dups VV))) &amp;&amp; (VV == ys) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
<span class=hs-linenum>152: </span><span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varop'>++</span> <span class='hs-varid'>ys</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
y:a
-&gt; ys:[{VV : a&lt;p y&gt; | true}]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | ((dups VV) == (if ((Set_mem y (listElts ys))) then (Set_cup (Set_sng y) (dups ys)) else (dups ys))) &amp;&amp; ((len VV) == (1 + (len ys))) &amp;&amp; ((listElts VV) == (Set_cup (Set_sng y) (listElts ys)))}</span><span class='hs-conop'>:</span></a><span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>xs:{VV : [a] | ((Set_emp (dups VV)))}
-&gt; ys:{VV : [a] | ((Set_emp (Set_cap (listElts VV) (listElts xs)))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((listElts VV) == (Set_cup (listElts xs) (listElts ys)))}</span><span class='hs-varop'>++</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | ((Set_emp (dups VV))) &amp;&amp; (VV == ys) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span>
</pre>

Reverse
-------

Next, we can prove that if a unique list is reversed, 
the output list has the same elements as the input,
and also it is unique.


<pre><span class=hs-linenum>163: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reverse</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>UList</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>UList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>| (EqElts v xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>164: </span><span class='hs-definition'>reverse</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>165: </span><a class=annot href="#"><span class=annottext>forall a.
xs:{VV : [a] | ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((listElts VV) == (listElts xs))}</span><span class='hs-definition'>reverse</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | ((Set_emp (dups VV))) &amp;&amp; ((len VV) == 0)}
-&gt; x2:{VV : [a] | ((Set_emp (Set_cap (listElts VV) (listElts x1)))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((listElts VV) == (Set_cup (listElts x1) (listElts x2))) &amp;&amp; ((listElts VV) == (Set_cup (listElts x2) (listElts x1))) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | ((Set_emp (dups VV))) &amp;&amp; ((Set_emp (listElts VV))) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>166: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>167: </span>    <a class=annot href="#"><span class=annottext>a:{VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((len VV) &gt;= 0)}
-&gt; x1:{VV : [a] | ((Set_emp (Set_cap (listElts VV) (listElts a)))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((listElts VV) == (Set_cup (listElts a) (listElts x1))) &amp;&amp; ((listElts VV) == (Set_cup (listElts x1) (listElts a))) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>go</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>a</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | ((Set_emp (dups VV))) &amp;&amp; (VV == a) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>a</span></a>
<span class=hs-linenum>168: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a:{VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((len VV) &gt;= 0)}
-&gt; x1:{VV : [a] | ((Set_emp (Set_cap (listElts VV) (listElts a)))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((listElts VV) == (Set_cup (listElts a) (listElts x1))) &amp;&amp; ((listElts VV) == (Set_cup (listElts x1) (listElts a))) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>go</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
y:a
-&gt; ys:[{VV : a&lt;p y&gt; | true}]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | ((dups VV) == (if ((Set_mem y (listElts ys))) then (Set_cup (Set_sng y) (dups ys)) else (dups ys))) &amp;&amp; ((len VV) == (1 + (len ys))) &amp;&amp; ((listElts VV) == (Set_cup (Set_sng y) (listElts ys)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | ((Set_emp (dups VV))) &amp;&amp; (VV == a) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>a</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> 
</pre>

Filter
------

Finally, filtering a unique list returns a list with a subset of
values of the input list, that once again is unique! 


<pre><span class=hs-linenum>178: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>filter</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>179: </span>           <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>UList</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>180: </span>           <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>UList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>| (SubElts v xs)}</span> 
<span class=hs-linenum>181: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>182: </span><a class=annot href="#"><span class=annottext>forall a.
(a -&gt; (GHC.Types.Bool))
-&gt; x2:{VV : [a] | ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((Set_sub (listElts VV) (listElts x2))) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-definition'>filter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>p</span></a> <span class='hs-conid'>[]</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
{VV : [{VV : a | false}]&lt;p&gt; | ((Set_emp (dups VV))) &amp;&amp; ((Set_emp (listElts VV))) &amp;&amp; ((len VV) == 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>183: </span><span class='hs-definition'>filter</span> <span class='hs-varid'>p</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>184: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>p</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
y:a
-&gt; ys:[{VV : a&lt;p y&gt; | true}]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | ((dups VV) == (if ((Set_mem y (listElts ys))) then (Set_cup (Set_sng y) (dups ys)) else (dups ys))) &amp;&amp; ((len VV) == (1 + (len ys))) &amp;&amp; ((listElts VV) == (Set_cup (Set_sng y) (listElts ys)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>forall a.
(a -&gt; (GHC.Types.Bool))
-&gt; x2:{VV : [a] | ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((Set_sub (listElts VV) (listElts x2))) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>p</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>185: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a.
(a -&gt; (GHC.Types.Bool))
-&gt; x2:{VV : [a] | ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((Set_sub (listElts VV) (listElts x2))) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>p</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>


Unique Zipper
=============

That was easy enough! Now, lets look at a slightly more interesting
structure fashioned from lists.  A [zipper][wiki-zipper] is an aggregate
data stucture that is used to arbitrary traverse the structure and update
its contents.

We define a zipper as a data type that contains an element (called `focus`)
that we are currently using, a list of elements (called `up`) before
the current one, and a list of elements (called `down`) after the current one.


<pre><span class=hs-linenum>202: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>Zipper</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Zipper</span> <span class='hs-layout'>{</span> <a class=annot href="#"><span class=annottext>forall a. (UniqueZipper.Zipper a) -&gt; a</span><span class='hs-varid'>focus</span></a> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span>       <span class='hs-comment'>-- focused element in this set</span>
<span class=hs-linenum>203: </span>                       <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>forall a. (UniqueZipper.Zipper a) -&gt; [a]</span><span class='hs-varid'>up</span></a>    <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>     <span class='hs-comment'>-- elements to the left</span>
<span class=hs-linenum>204: </span>                       <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>forall a. (UniqueZipper.Zipper a) -&gt; [a]</span><span class='hs-varid'>down</span></a>  <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-layout'>}</span>   <span class='hs-comment'>-- elements to the right</span>
</pre>


One well-known application of zippers is in the
[XMonad](http://xmonad.org/) tiling window manager. 
The set of windows being managed is stored in a zipper 
similar to the above. The `focus` happily coincides with 
the window currently in focus, and the `up` and `down` 
to the list of windows that come before and after it.

One crucial invariant maintained by XMonad is that the zipper structure is
unique -- i.e. each window appears at most once inside the zipper.

Lets see how we can state and check that all the values in a zipper are unique.

To start with, we would like to refine the `Zipper` data declaration
to express that both the lists in the structure are unique **and** 
do not include `focus` in their values.

LiquidHaskell allow us to refine data type declarations, using the liquid comments.
So, apart from above definition definition for the `Zipper`, we add a refined one,
stating that the data structure always enjoys the desired properties.


<pre><span class=hs-linenum>229: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>Zipper</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Zipper</span> <span class='hs-layout'>{</span> <span class='hs-varid'>focus</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>230: </span>                           <span class='hs-layout'>,</span> <span class='hs-varid'>up</span>    <span class='hs-keyglyph'>::</span> <span class='hs-conid'>UListDif</span> <span class='hs-varid'>a</span> <span class='hs-varid'>focus</span>
<span class=hs-linenum>231: </span>                           <span class='hs-layout'>,</span> <span class='hs-varid'>down</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>UListDif</span> <span class='hs-varid'>a</span> <span class='hs-varid'>focus</span><span class='hs-layout'>}</span>
<span class=hs-linenum>232: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>233: </span>
<span class=hs-linenum>234: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>UListDif</span> <span class='hs-varid'>a</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-conid'>UList</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>not</span> <span class='hs-layout'>(</span><span class='hs-conid'>ListElt</span> <span class='hs-conid'>N</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

It is worth noting that the above is kind of *dependent* record in that
the types of the `up` and `down` fields depend on the value of the `focus`
field.

With this annotation any time we use a `Zipper` in the code LiquidHaskell
knows that the `up` and `down` components are unique lists
that do not include `focus`. Moreover, when a new `Zipper` is constructed
LiquidHaskell proves that this property holds, otherwise a liquid type 
error is reported.


Hold on a minute!

The awake reader will have noticed that values inside the `Zipper` as 
specified so far, are *not unique*, as nothing prevents a value from 
appearing in both the `up` and the `down` components.

So, we have to specify that the contents of those two fields are *disjoint*.

One way to achieve this is by defining two measures `getUp` and `getDown`
that return the relevant parts of the `Zipper`


<pre><span class=hs-linenum>260: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>getUp</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span><span class='hs-varop'>.</span> <span class='hs-layout'>(</span><span class='hs-conid'>Zipper</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> 
<span class=hs-linenum>261: </span>    <span class='hs-varid'>getUp</span> <span class='hs-layout'>(</span><span class='hs-conid'>Zipper</span> <span class='hs-varid'>focus</span> <span class='hs-varid'>up</span> <span class='hs-varid'>down</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>up</span>
<span class=hs-linenum>262: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>263: </span>
<span class=hs-linenum>264: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>getDown</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span><span class='hs-varop'>.</span> <span class='hs-layout'>(</span><span class='hs-conid'>Zipper</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> 
<span class=hs-linenum>265: </span>    <span class='hs-varid'>getDown</span> <span class='hs-layout'>(</span><span class='hs-conid'>Zipper</span> <span class='hs-varid'>focus</span> <span class='hs-varid'>up</span> <span class='hs-varid'>down</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>down</span>
<span class=hs-linenum>266: </span>  <span class='hs-keyword'>@-}</span>
</pre>

With these definitions, we create a type alias `UZipper`
that states that the two list components are disjoint, and hence,
that we have a *unique zipper* with no duplicates.


<pre><span class=hs-linenum>274: </span><span class='hs-keyword'>{-@</span> 
<span class=hs-linenum>275: </span>  <span class='hs-keyword'>type</span> <span class='hs-conid'>UZipper</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Zipper</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-conid'>DisjointElts</span> <span class='hs-layout'>(</span><span class='hs-varid'>getUp</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>getDown</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span> 
<span class=hs-linenum>276: </span>  <span class='hs-keyword'>@-}</span>
</pre>


Functions on Unique Zippers
===========================

Now that we have defined a unique zipper, it is straightforward for
LiquidHaskell to prove that operations on zippers preserve uniqueness.

Differentiation
---------------

We can prove that a zipper that built from elements from a unique list is
indeed unique.


<pre><span class=hs-linenum>293: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>differentiate</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>UList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Maybe</span> <span class='hs-layout'>(</span><span class='hs-conid'>UZipper</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>294: </span><a class=annot href="#"><span class=annottext>forall a.
{VV : [a] | ((Set_emp (dups VV)))}
-&gt; (Data.Maybe.Maybe {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))})</span><span class='hs-definition'>differentiate</span></a> <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall a. {VV : (Data.Maybe.Maybe a) | (((isJust VV)) &lt;=&gt; false)}</span><span class='hs-conid'>Nothing</span></a>
<span class=hs-linenum>295: </span><span class='hs-definition'>differentiate</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; {VV : (Data.Maybe.Maybe {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}) | (((isJust VV)) &lt;=&gt; true) &amp;&amp; ((fromJust VV) == x)}</span><span class='hs-conid'>Just</span></a> <a class=annot href="#"><span class=annottext>({VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
 -&gt; (Data.Maybe.Maybe {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}))
-&gt; {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; (Data.Maybe.Maybe {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))})</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>focus:a
-&gt; up:{VV : [a] | (not (((Set_mem focus (listElts VV))))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; down:{VV : [a] | (not (((Set_mem focus (listElts VV))))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; {VV : (UniqueZipper.Zipper a) | ((getDown VV) == down) &amp;&amp; ((getUp VV) == up)}</span><span class='hs-conid'>Zipper</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | ((Set_emp (dups VV))) &amp;&amp; ((Set_emp (listElts VV))) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-conid'>[]</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == xs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

Integration
-----------

And vice versa, all elements of a unique zipper yield a unique list.


<pre><span class=hs-linenum>304: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>integrate</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>UZipper</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>UList</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>305: </span><a class=annot href="#"><span class=annottext>forall a.
{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; {VV : [a] | ((Set_emp (dups VV)))}</span><span class='hs-definition'>integrate</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Zipper</span> <span class='hs-varid'>x</span> <span class='hs-varid'>l</span> <span class='hs-varid'>r</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>xs:{VV : [a] | ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((listElts VV) == (listElts xs))}</span><span class='hs-varid'>reverse</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (not (((Set_mem x (listElts VV))))) &amp;&amp; ((Set_emp (dups VV))) &amp;&amp; (VV == l) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>l</span></a> <a class=annot href="#"><span class=annottext>xs:{VV : [a] | ((Set_emp (dups VV)))}
-&gt; ys:{VV : [a] | ((Set_emp (Set_cap (listElts VV) (listElts xs)))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((listElts VV) == (Set_cup (listElts xs) (listElts ys)))}</span><span class='hs-varop'>++</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
y:a
-&gt; ys:[{VV : a&lt;p y&gt; | true}]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | ((dups VV) == (if ((Set_mem y (listElts ys))) then (Set_cup (Set_sng y) (dups ys)) else (dups ys))) &amp;&amp; ((len VV) == (1 + (len ys))) &amp;&amp; ((listElts VV) == (Set_cup (Set_sng y) (listElts ys)))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (not (((Set_mem x (listElts VV))))) &amp;&amp; ((Set_emp (dups VV))) &amp;&amp; (VV == r) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>r</span></a>
</pre>

Recall the types for `++` and `reverse` that we proved earlier -- hover
your mouse over the identifiers to refresh your memory. Those types are
essential for establishing the type of `integrate`. 

- By the definition of `UZipper` we know that `l` is a unique list
  and that `x` is not an element of `l`.

- Thus via the type of `reverse` we know that  `reverse l` is also
  unique and disjoint from `x` and `r`.

- Finally, using the previously established type for `++` 
  LiquidHaskell can prove that since `x : r` is a unique 
  list with elements disjoint from `reverse l` the concatenation
  of the two lists is also a unique list.


With the exact same reasoning, we use the above list operations to create more zipper operations.

Reverse
-------

We can reverse a unique zipper


<pre><span class=hs-linenum>332: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reverseZipper</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>UZipper</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>UZipper</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>333: </span><span class='hs-definition'>reverseZipper</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Zipper</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Zipper</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>334: </span><a class=annot href="#"><span class=annottext>forall a.
{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}</span><span class='hs-definition'>reverseZipper</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Zipper</span> <span class='hs-varid'>t</span> <span class='hs-varid'>ls</span> <span class='hs-varid'>rs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>focus:a
-&gt; up:{VV : [a] | (not (((Set_mem focus (listElts VV))))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; down:{VV : [a] | (not (((Set_mem focus (listElts VV))))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; {VV : (UniqueZipper.Zipper a) | ((getDown VV) == down) &amp;&amp; ((getUp VV) == up)}</span><span class='hs-conid'>Zipper</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == t)}</span><span class='hs-varid'>t</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (not (((Set_mem t (listElts VV))))) &amp;&amp; ((Set_emp (dups VV))) &amp;&amp; (VV == rs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>rs</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (not (((Set_mem t (listElts VV))))) &amp;&amp; ((Set_emp (dups VV))) &amp;&amp; (VV == ls) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>ls</span></a>
</pre>

Shifting Focus
--------------

More the focus up or down


<pre><span class=hs-linenum>343: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>focusUp</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>UZipper</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>UZipper</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>344: </span><a class=annot href="#"><span class=annottext>forall a.
{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}</span><span class='hs-definition'>focusUp</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Zipper</span> <span class='hs-varid'>t</span> <span class='hs-conid'>[]</span> <span class='hs-varid'>rs</span><span class='hs-layout'>)</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>focus:a
-&gt; up:{VV : [a] | (not (((Set_mem focus (listElts VV))))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; down:{VV : [a] | (not (((Set_mem focus (listElts VV))))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; {VV : (UniqueZipper.Zipper a) | ((getDown VV) == down) &amp;&amp; ((getUp VV) == up)}</span><span class='hs-conid'>Zipper</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == x) &amp;&amp; (VV == x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (not (((Set_mem x (listElts VV))))) &amp;&amp; (not (((Set_mem x (listElts VV))))) &amp;&amp; ((Set_emp (dups VV))) &amp;&amp; (VV == xs) &amp;&amp; (VV == xs) &amp;&amp; ((len VV) == (len xs)) &amp;&amp; ((listElts VV) == (Set_cup (listElts xs) (listElts xs))) &amp;&amp; ((listElts VV) == (listElts xs)) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | ((Set_emp (dups VV))) &amp;&amp; ((Set_emp (listElts VV))) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-conid'>[]</span></a> 
<span class=hs-linenum>345: </span>  <span class='hs-keyword'>where</span> 
<span class=hs-linenum>346: </span>    <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == x)}</span><span class='hs-varid'>x</span></a><span class='hs-conop'>:</span><a class=annot href="#"><span class=annottext>{VV : [a] | (not (((Set_mem x (listElts VV))))) &amp;&amp; (not (((Set_mem x (listElts VV))))) &amp;&amp; ((Set_emp (dups VV))) &amp;&amp; (VV == xs) &amp;&amp; ((len VV) == (len xs)) &amp;&amp; ((listElts VV) == (Set_cup (listElts xs) (listElts xs))) &amp;&amp; ((listElts VV) == (listElts xs)) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>                   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>xs:{VV : [a] | ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((listElts VV) == (listElts xs))}</span><span class='hs-varid'>reverse</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == t)}</span><span class='hs-varid'>t</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
y:a
-&gt; ys:[{VV : a&lt;p y&gt; | true}]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | ((dups VV) == (if ((Set_mem y (listElts ys))) then (Set_cup (Set_sng y) (dups ys)) else (dups ys))) &amp;&amp; ((len VV) == (1 + (len ys))) &amp;&amp; ((listElts VV) == (Set_cup (Set_sng y) (listElts ys)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (not (((Set_mem t (listElts VV))))) &amp;&amp; ((Set_emp (dups VV))) &amp;&amp; (VV == rs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>rs</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>347: </span>
<span class=hs-linenum>348: </span><span class='hs-definition'>focusUp</span> <span class='hs-layout'>(</span><span class='hs-conid'>Zipper</span> <span class='hs-varid'>t</span> <span class='hs-layout'>(</span><span class='hs-varid'>l</span><span class='hs-conop'>:</span><span class='hs-varid'>ls</span><span class='hs-layout'>)</span> <span class='hs-varid'>rs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>focus:a
-&gt; up:{VV : [a] | (not (((Set_mem focus (listElts VV))))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; down:{VV : [a] | (not (((Set_mem focus (listElts VV))))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; {VV : (UniqueZipper.Zipper a) | ((getDown VV) == down) &amp;&amp; ((getUp VV) == up)}</span><span class='hs-conid'>Zipper</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == l)}</span><span class='hs-varid'>l</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == ls) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>ls</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == t)}</span><span class='hs-varid'>t</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
y:a
-&gt; ys:[{VV : a&lt;p y&gt; | true}]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | ((dups VV) == (if ((Set_mem y (listElts ys))) then (Set_cup (Set_sng y) (dups ys)) else (dups ys))) &amp;&amp; ((len VV) == (1 + (len ys))) &amp;&amp; ((listElts VV) == (Set_cup (Set_sng y) (listElts ys)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (not (((Set_mem t (listElts VV))))) &amp;&amp; ((Set_emp (dups VV))) &amp;&amp; (VV == rs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>rs</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>349: </span>
<span class=hs-linenum>350: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>focusDown</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>UZipper</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>UZipper</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>351: </span><a class=annot href="#"><span class=annottext>forall a.
{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}</span><span class='hs-definition'>focusDown</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}</span><span class='hs-varid'>reverseZipper</span></a> <a class=annot href="#"><span class=annottext>forall &lt;q :: (UniqueZipper.Zipper a)-&gt; (UniqueZipper.Zipper a)-&gt; Bool, p :: (UniqueZipper.Zipper a)-&gt; (UniqueZipper.Zipper a)-&gt; Bool&gt;.
(x:{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
 -&gt; {VV : (UniqueZipper.Zipper a)&lt;p x&gt; | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))})
-&gt; (y:{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
    -&gt; {VV : (UniqueZipper.Zipper a)&lt;q y&gt; | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))})
-&gt; x:{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; exists [z:{VV : (UniqueZipper.Zipper a)&lt;q x&gt; | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}].{VV : (UniqueZipper.Zipper a)&lt;p z&gt; | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}</span><span class='hs-varid'>focusUp</span></a> <a class=annot href="#"><span class=annottext>forall &lt;q :: (UniqueZipper.Zipper a)-&gt; (UniqueZipper.Zipper a)-&gt; Bool, p :: (UniqueZipper.Zipper a)-&gt; (UniqueZipper.Zipper a)-&gt; Bool&gt;.
(x:{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
 -&gt; {VV : (UniqueZipper.Zipper a)&lt;p x&gt; | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))})
-&gt; (y:{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
    -&gt; {VV : (UniqueZipper.Zipper a)&lt;q y&gt; | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))})
-&gt; x:{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; exists [z:{VV : (UniqueZipper.Zipper a)&lt;q x&gt; | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}].{VV : (UniqueZipper.Zipper a)&lt;p z&gt; | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}</span><span class='hs-varid'>reverseZipper</span></a>
</pre>

Filter
------

Finally, using the filter operation on lists allows LiquidHaskell to prove
that filtering a zipper also preserves uniqueness.


<pre><span class=hs-linenum>361: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>filterZipper</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>UZipper</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Maybe</span> <span class='hs-layout'>(</span><span class='hs-conid'>UZipper</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>362: </span><a class=annot href="#"><span class=annottext>forall a.
(a -&gt; (GHC.Types.Bool))
-&gt; {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; (Data.Maybe.Maybe {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))})</span><span class='hs-definition'>filterZipper</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>p</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Zipper</span> <span class='hs-varid'>f</span> <span class='hs-varid'>ls</span> <span class='hs-varid'>rs</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>363: </span>  <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>case</span> <a class=annot href="#"><span class=annottext>(a -&gt; (GHC.Types.Bool))
-&gt; xs:{VV : [a] | ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((Set_sub (listElts VV) (listElts xs)))}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>p</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV == f)}</span><span class='hs-varid'>f</span></a><a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
y:a
-&gt; ys:[{VV : a&lt;p y&gt; | true}]&lt;p&gt;
-&gt; {VV : [a]&lt;p&gt; | ((dups VV) == (if ((Set_mem y (listElts ys))) then (Set_cup (Set_sng y) (dups ys)) else (dups ys))) &amp;&amp; ((len VV) == (1 + (len ys))) &amp;&amp; ((listElts VV) == (Set_cup (Set_sng y) (listElts ys)))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (not (((Set_mem f (listElts VV))))) &amp;&amp; ((Set_emp (dups VV))) &amp;&amp; (VV == rs) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>rs</span></a><span class='hs-layout'>)</span> <span class='hs-keyword'>of</span>
<span class=hs-linenum>364: </span>      <span class='hs-varid'>f'</span><span class='hs-conop'>:</span><span class='hs-varid'>rs'</span> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>x:{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; {VV : (Data.Maybe.Maybe {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}) | (((isJust VV)) &lt;=&gt; true) &amp;&amp; ((fromJust VV) == x)}</span><span class='hs-conid'>Just</span></a> <a class=annot href="#"><span class=annottext>({VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
 -&gt; (Data.Maybe.Maybe {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}))
-&gt; {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; (Data.Maybe.Maybe {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))})</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>focus:a
-&gt; up:{VV : [a] | (not (((Set_mem focus (listElts VV))))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; down:{VV : [a] | (not (((Set_mem focus (listElts VV))))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; {VV : (UniqueZipper.Zipper a) | ((getDown VV) == down) &amp;&amp; ((getUp VV) == up)}</span><span class='hs-conid'>Zipper</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == f')}</span><span class='hs-varid'>f'</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(a -&gt; (GHC.Types.Bool))
-&gt; xs:{VV : [a] | ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((Set_sub (listElts VV) (listElts xs)))}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>p</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (not (((Set_mem f (listElts VV))))) &amp;&amp; ((Set_emp (dups VV))) &amp;&amp; (VV == ls) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>ls</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == rs') &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>rs'</span></a>
<span class=hs-linenum>365: </span>      <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>case</span> <a class=annot href="#"><span class=annottext>(a -&gt; (GHC.Types.Bool))
-&gt; xs:{VV : [a] | ((Set_emp (dups VV)))}
-&gt; {VV : [a] | ((Set_emp (dups VV))) &amp;&amp; ((Set_sub (listElts VV) (listElts xs)))}</span><span class='hs-varid'>filter</span></a> <a class=annot href="#"><span class=annottext>a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>p</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (not (((Set_mem f (listElts VV))))) &amp;&amp; ((Set_emp (dups VV))) &amp;&amp; (VV == ls) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>ls</span></a> <span class='hs-keyword'>of</span>                  
<span class=hs-linenum>366: </span>                  <span class='hs-varid'>f'</span><span class='hs-conop'>:</span><span class='hs-varid'>ls'</span> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>x:{VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; {VV : (Data.Maybe.Maybe {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}) | (((isJust VV)) &lt;=&gt; true) &amp;&amp; ((fromJust VV) == x)}</span><span class='hs-conid'>Just</span></a> <a class=annot href="#"><span class=annottext>({VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
 -&gt; (Data.Maybe.Maybe {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}))
-&gt; {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))}
-&gt; (Data.Maybe.Maybe {VV : (UniqueZipper.Zipper a) | ((Set_emp (Set_cap (listElts (getUp VV)) (listElts (getDown VV)))))})</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>focus:a
-&gt; up:{VV : [a] | (not (((Set_mem focus (listElts VV))))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; down:{VV : [a] | (not (((Set_mem focus (listElts VV))))) &amp;&amp; ((Set_emp (dups VV)))}
-&gt; {VV : (UniqueZipper.Zipper a) | ((getDown VV) == down) &amp;&amp; ((getUp VV) == up)}</span><span class='hs-conid'>Zipper</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV == f')}</span><span class='hs-varid'>f'</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV == ls') &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-varid'>ls'</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}]&lt;\_ VV -&gt; false&gt; | ((Set_emp (dups VV))) &amp;&amp; ((Set_emp (listElts VV))) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>367: </span>                  <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>forall a. {VV : (Data.Maybe.Maybe a) | (((isJust VV)) &lt;=&gt; false)}</span><span class='hs-conid'>Nothing</span></a>
</pre>

Conclusion
==========

That's all for now! This post illustrated

1. How we can use set theory to express properties the values of the list,
   such as list uniqueness.

2. How we can use LuquidHaskell to prove that these properties are
   preserved through list operations.

3. How we can embed this properties in complicated data structures that use
   lists, such as a zipper.


[wiki-zipper]: http://en.wikipedia.org/wiki/Zipper_(data_structure)
[about-sets]:  blog/2013/03/26/talking-about-sets.lhs/
[setspec]:     https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/Set.spec


<pre><span class=hs-linenum>390: </span><span class='hs-comment'>-- TODO: Dummy function to provide qualifier hint.</span>
<span class=hs-linenum>391: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>q</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span>  <span class='hs-keyword'>{v:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>|(not (Set_mem x (listElts v)))}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>392: </span><span class='hs-definition'>q</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>393: </span><a class=annot href="#"><span class=annottext>forall a. x:a -&gt; {VV : [a] | (not (((Set_mem x (listElts VV)))))}</span><span class='hs-definition'>q</span></a> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: a-&gt; a-&gt; Bool&gt;.
{VV : [{VV : a | false}]&lt;p&gt; | ((Set_emp (dups VV))) &amp;&amp; ((Set_emp (listElts VV))) &amp;&amp; ((len VV) == 0)}</span><span class='hs-conid'>[]</span></a>
</pre>


