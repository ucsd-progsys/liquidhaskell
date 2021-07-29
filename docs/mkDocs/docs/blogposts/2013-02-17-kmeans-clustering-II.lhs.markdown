---
layout: post
title: KMeans Clustering II
date: 2013-02-17 16:12
author: Ranjit Jhala
published: true
comments: true
tags: basic, measures
demo: KMeans.hs
---

**The story so far:** [Previously][kmeansI] we saw

- how to encode `n`-dimensional points using plain old Haskell lists,
- how to encode a matrix with `r` rows and `c` columns as a list of lists,
- some basic operations on points and matrices via list-manipulating functions

More importantly, we saw how easy it was to encode dimensionality with refinements over
the `len` measure, thereby allowing LiquidHaskell to precisely track the dimensions across
the various operations.

Next, lets use the basic types and operations to develop the actual *KMeans clustering*
algorithm, and, along the way, see how LiquidHaskell lets us write precise module
contracts which will ward against various unpleasant *lumpenexceptions*.

<!-- more -->


<pre><span class=hs-linenum>30: </span><span class='hs-comment'>{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}</span>
<span class=hs-linenum>31: </span>
<span class=hs-linenum>32: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>KMeans</span> <span class='hs-layout'>(</span><span class='hs-varid'>kmeans</span><span class='hs-layout'>,</span> <span class='hs-varid'>kmeansGen</span><span class='hs-layout'>)</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>33: </span>
<span class=hs-linenum>34: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>KMeansHelper</span>
<span class=hs-linenum>35: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span>              <span class='hs-varid'>hiding</span>      <span class='hs-layout'>(</span><span class='hs-varid'>zipWith</span><span class='hs-layout'>)</span>
<span class=hs-linenum>36: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>List</span>                        <span class='hs-layout'>(</span><span class='hs-varid'>sort</span><span class='hs-layout'>,</span> <span class='hs-varid'>span</span><span class='hs-layout'>,</span> <span class='hs-varid'>minimumBy</span><span class='hs-layout'>)</span>
<span class=hs-linenum>37: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Function</span>                    <span class='hs-layout'>(</span><span class='hs-varid'>on</span><span class='hs-layout'>)</span>
<span class=hs-linenum>38: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Ord</span>                         <span class='hs-layout'>(</span><span class='hs-varid'>comparing</span><span class='hs-layout'>)</span>
<span class=hs-linenum>39: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span>  <span class='hs-layout'>(</span><span class='hs-varid'>liquidAssert</span><span class='hs-layout'>,</span> <span class='hs-varid'>liquidError</span><span class='hs-layout'>)</span>
<span class=hs-linenum>40: </span>
<span class=hs-linenum>41: </span><span class='hs-keyword'>instance</span> <a class=annot href="#"><span class=annottext>(GHC.Classes.Eq (KMeans.WrapType [GHC.Types.Double] a))</span><span class='hs-conid'>Eq</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>WrapType</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Double</span><span class='hs-keyglyph'>]</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>42: </span>   <span class='hs-layout'>(</span><span class='hs-varop'>==</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:{VV : [{VV : (GHC.Types.Double) | false}] | false}
-&gt; y:{VV : [{VV : (GHC.Types.Double) | false}] | false}
-&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x = y))}</span><span class='hs-layout'>(</span></a><span class='hs-varop'>==</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>({VV : [{VV : (GHC.Types.Double) | false}] | false}
 -&gt; {VV : [{VV : (GHC.Types.Double) | false}] | false}
 -&gt; {VV : (GHC.Types.Bool) | false})
-&gt; ({VV : (KMeans.WrapType {VV : [{VV : (GHC.Types.Double) | false}] | false} {VV : a | false}) | false}
    -&gt; {VV : [{VV : (GHC.Types.Double) | false}] | false})
-&gt; {VV : (KMeans.WrapType {VV : [{VV : (GHC.Types.Double) | false}] | false} {VV : a | false}) | false}
-&gt; {VV : (KMeans.WrapType {VV : [{VV : (GHC.Types.Double) | false}] | false} {VV : a | false}) | false}
-&gt; {VV : (GHC.Types.Bool) | false}</span><span class='hs-varop'>`on`</span></a> <a class=annot href="#"><span class=annottext>(KMeans.WrapType {VV : [{VV : (GHC.Types.Double) | false}] | false} {VV : a | false})
-&gt; {VV : [{VV : (GHC.Types.Double) | false}] | false}</span><span class='hs-varid'>getVect</span></a>
<span class=hs-linenum>43: </span>
<span class=hs-linenum>44: </span><span class='hs-keyword'>instance</span> <a class=annot href="#"><span class=annottext>(GHC.Classes.Ord (KMeans.WrapType [GHC.Types.Double] a))</span><span class='hs-conid'>Ord</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>WrapType</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Double</span><span class='hs-keyglyph'>]</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>45: </span>    <span class='hs-varid'>compare</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(GHC.Classes.Ord [GHC.Types.Double])</span><span class='hs-varid'>comparing</span></a> <a class=annot href="#"><span class=annottext>(KMeans.WrapType {VV : [{VV : (GHC.Types.Double) | false}] | false} {VV : a | false})
-&gt; {VV : [{VV : (GHC.Types.Double) | false}] | false}</span><span class='hs-varid'>getVect</span></a>
</pre>

Recall that we are using a modified version of an [existing KMeans implementation][URL-kmeans].
While not the swiftest implementation, it serves as a nice introduction to the algorithm,
and the general invariants carry over to more sophisticated implementations.

A Quick Recap
-------------

Before embarking on the journey, lets remind ourselves of our destination:
the goal of [K-Means clustering](http://en.wikipedia.org/wiki/K-means_clustering) is

- **Take as Input** : A set of *points* represented by *n-dimensional points* in *Euclidian* space

- **Return as Ouptut** : A partitioning of the points, into upto K clusters, in a manner that
  minimizes the sum of distances between each point and its cluster center.

Last time, we introduced a variety of refinement type aliases for Haskell lists

 **Fixed Length Lists**
<pre><span class=hs-linenum>66: </span><span class='hs-keyword'>type</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span><span class='hs-layout'>}</span>
</pre>

 **Non-empty Lists**
<pre><span class=hs-linenum>70: </span><span class='hs-keyword'>type</span> <span class='hs-conid'>NonEmptyList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-varop'>&gt;</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span>
</pre>

 **N-Dimensional Points**
<pre><span class=hs-linenum>74: </span><span class='hs-keyword'>type</span> <span class='hs-conid'>Point</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>List</span> <span class='hs-conid'>Double</span> <span class='hs-conid'>N</span>
</pre>

 **Matrices**
<pre><span class=hs-linenum>78: </span><span class='hs-keyword'>type</span> <span class='hs-conid'>Matrix</span> <span class='hs-varid'>a</span> <span class='hs-conid'>Rows</span> <span class='hs-conid'>Cols</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>List</span> <span class='hs-layout'>(</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-conid'>Cols</span><span class='hs-layout'>)</span> <span class='hs-conid'>Rows</span>
</pre>

 We also saw several basic list operations
<pre><span class=hs-linenum>82: </span><span class='hs-definition'>groupBy</span>   <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Clustering</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>83: </span><span class='hs-definition'>partition</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>PosInt</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Clustering</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>84: </span><span class='hs-definition'>zipWith</span>   <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>c</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>List</span> <span class='hs-varid'>b</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>List</span> <span class='hs-varid'>c</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>85: </span><span class='hs-definition'>transpose</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>c</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>r</span><span class='hs-conop'>:</span><span class='hs-conid'>PosInt</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Matrix</span> <span class='hs-varid'>a</span> <span class='hs-varid'>r</span> <span class='hs-varid'>c</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Matrix</span> <span class='hs-varid'>a</span> <span class='hs-varid'>c</span> <span class='hs-varid'>r</span>
</pre>

whose types will prove essential in order to verify the invariants of the
clustering algorithm. You might open the [previous episode][kmeansI] in a
separate tab to keep those functions handy, but fear not, we will refresh
our memory about them when we get around to using them below.

Generalized Points
------------------

To be more flexible, we will support *arbitrary* points as long as they can
be **projected** to Euclidian space. In addition to supporting, say, an
image or a [cat video][maru] as a point, this will allow us to *weight*
different dimensions to different degrees.

We represent generalized points with a record


<pre><span class=hs-linenum>104: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>WrapType</span> <span class='hs-varid'>b</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>WrapType</span> <span class='hs-layout'>{</span><a class=annot href="#"><span class=annottext>(KMeans.WrapType a b) -&gt; a</span><span class='hs-varid'>getVect</span></a> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>b</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>(KMeans.WrapType a b) -&gt; b</span><span class='hs-varid'>getVal</span></a> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span><span class='hs-layout'>}</span>
</pre>

and we can define an alias that captures the dimensionality of the point


<pre><span class=hs-linenum>110: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>GenPoint</span> <span class='hs-varid'>a</span> <span class='hs-conid'>N</span>  <span class='hs-keyglyph'>=</span> <span class='hs-conid'>WrapType</span> <span class='hs-layout'>(</span><span class='hs-conid'>Point</span> <span class='hs-conid'>N</span><span class='hs-layout'>)</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>@-}</span>
</pre>

That is, `GenPoint a N` denotes a general `a` value that has an
`N`-dimensional projection into Euclidean space.

Algorithm: Iterative Clustering
-------------------------------

Terrific, now that all the pieces are in place lets look at the KMeans
algorithm. We have implemented a function `kmeans'`, which takes as input a
dimension `n`, the maximum number of clusters `k` (which must be positive),
a list of *generalized points* of dimension `n`, and returns a `Clustering`
(i.e. a list of *non-empty lists*) of the generalized points.

So much verbiage -- a type is worth a thousand comments!


<pre><span class=hs-linenum>128: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>kmeans'</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span>
<span class=hs-linenum>129: </span>            <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>k</span><span class='hs-conop'>:</span><span class='hs-conid'>PosInt</span>
<span class=hs-linenum>130: </span>            <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>points</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-conid'>GenPoint</span> <span class='hs-varid'>a</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>131: </span>            <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Clustering</span> <span class='hs-layout'>(</span><span class='hs-conid'>GenPoint</span> <span class='hs-varid'>a</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>

There! Crisp and to the point. Sorry. Anyhoo, the function implements the
above type.


<pre><span class=hs-linenum>138: </span><a class=annot href="#"><span class=annottext>n:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV &gt; 0)}
-&gt; [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)]
-&gt; [{v : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (len([v]) &gt; 0)}]</span><span class='hs-definition'>kmeans'</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt; 0)}</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>[(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)]</span><span class='hs-varid'>points</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(GHC.Classes.Eq [[KMeans.WrapType [GHC.Types.Double] a]])</span><span class='hs-varid'>fixpoint</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>n:(GHC.Types.Int)
-&gt; [{v : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (len([v]) &gt; 0)}]
-&gt; [{v : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (len([v]) &gt; 0)}]</span><span class='hs-varid'>refineCluster</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = n)}</span><span class='hs-varid'>n</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                            (len([VV]) = n)} a)] | (len([VV]) &gt; 0)}] | (VV = initialClustering),
                                                                                                       (len([VV]) &gt;= 0)}</span><span class='hs-varid'>initialClustering</span></a>
<span class=hs-linenum>139: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>140: </span>    <a class=annot href="#"><span class=annottext>[{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                      (len([VV]) = n)} a)] | (len([VV]) &gt; 0)}]</span><span class='hs-varid'>initialClustering</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt; 0)}
-&gt; [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                  (len([VV]) = n)} a)]
-&gt; [{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                         (len([VV]) = n)} a)] | (len([VV]) &gt; 0)}]</span><span class='hs-varid'>partition</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = clusterSize)}</span><span class='hs-varid'>clusterSize</span></a> <a class=annot href="#"><span class=annottext>{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (VV = points),
                                                                            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>points</span></a>
<span class=hs-linenum>141: </span>    <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>clusterSize</span></a>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV = ((x &gt; y) ? x : y))}</span><span class='hs-varid'>max</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>xs:[(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                  (len([VV]) = n)} a)]
-&gt; {VV : (GHC.Types.Int) | (VV = len([xs]))}</span><span class='hs-varid'>length</span></a> <a class=annot href="#"><span class=annottext>{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (VV = points),
                                                                            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>points</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = k),(VV &gt; 0)}</span><span class='hs-varid'>k</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x - y))}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x / y))}</span><span class='hs-varop'>`div`</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = k),(VV &gt; 0)}</span><span class='hs-varid'>k</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>142: </span>
<span class=hs-linenum>143: </span>    <span class='hs-varid'>fixpoint</span>          <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Eq</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>144: </span>    <a class=annot href="#"><span class=annottext>(GHC.Classes.Eq a) -&gt; (a -&gt; a) -&gt; a -&gt; a</span><span class='hs-varid'>fixpoint</span></a> <a class=annot href="#"><span class=annottext>a -&gt; a</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>x</span></a>      <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>if</span> <a class=annot href="#"><span class=annottext>(GHC.Types.Bool)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>a -&gt; a</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>x:a
-&gt; y:a -&gt; {VV : (GHC.Types.Bool) | ((? Prop([VV])) &lt;=&gt; (x = y))}</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <span class='hs-keyword'>then</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <span class='hs-keyword'>else</span> <a class=annot href="#"><span class=annottext>(GHC.Classes.Eq a) -&gt; (a -&gt; a) -&gt; a -&gt; a</span><span class='hs-varid'>fixpoint</span></a> <a class=annot href="#"><span class=annottext>a -&gt; a</span><span class='hs-varid'>f</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>a -&gt; a</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span>
</pre>

That is, `kmeans'` creates an `initialClustering` by
`partition`-ing the `points` into chunks with `clusterSize` elements.
Then, it invokes `fixpoint` to *iteratively refine* the initial
clustering  with `refineCluster` until it converges to a stable
clustering that cannot be improved upon. This stable clustering
is returned as the output.

LiquidHaskell verifies that `kmeans'` adheres to the given signature in two steps.

**1. Initial Clustering**

 First, LiquidHaskell determines from
<pre><span class=hs-linenum>159: </span><span class='hs-definition'>max</span>       <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>v</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>x</span><span class='hs-layout'>)</span> <span class='hs-varop'>&amp;&amp;</span> <span class='hs-layout'>(</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&gt;=</span> <span class='hs-varid'>y</span><span class='hs-layout'>)</span> <span class='hs-layout'>}</span>
</pre>

 that `clusterSize` is strictly positive, and hence, from
<pre><span class=hs-linenum>163: </span><span class='hs-definition'>partition</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>size</span><span class='hs-conop'>:</span><span class='hs-conid'>PosInt</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Clustering</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
</pre>

which we saw [last time][kmeansI], that `initialClustering` is indeed
a valid `Clustering` of `(GenPoint a n)`.

**2. Fixpoint**

Next, LiquidHaskell infers that at the call `fixpoint (refineCluster n)
...`, that the type parameter `a` of `fixpoint` can be *instantiated* with
`Clustering (GenPoint a n)`.  This is because `initialClustering` is a
valid clustering, as we saw above, and because `refineCluster` takes -- and
returns -- valid `n`-dimensional clusterings, as we shall see below.
Consequently, the value returned by `kmeans'` is also `Clustering` of
`GenPoint a n` as required.

Refining A Clustering
---------------------

Thus, the real work in KMeans happens inside `refineCluster`, which takes a
clustering and improves it, like so:


<pre><span class=hs-linenum>186: </span><a class=annot href="#"><span class=annottext>n:(GHC.Types.Int)
-&gt; [{v : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (len([v]) &gt; 0)}]
-&gt; [{v : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (len([v]) &gt; 0)}]</span><span class='hs-definition'>refineCluster</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>[{v : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (len([v]) &gt; 0)}]</span><span class='hs-varid'>clusters</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                            (len([VV]) = n),
                                                            (len([VV]) &gt;= 0)} a)] | (len([VV]) &gt; 0)}] | (VV = clusters'),
                                                                                                        (len([VV]) = len([centeredGroups])),
                                                                                                        (len([VV]) &gt;= 0)}</span><span class='hs-varid'>clusters'</span></a>
<span class=hs-linenum>187: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>188: </span>    <span class='hs-comment'>-- 1. Compute cluster centers</span>
<span class=hs-linenum>189: </span>    <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Double)] | (n = len([VV])),
                                    (len([VV]) = n)}] | (len([VV]) = len([clusters]))}</span><span class='hs-varid'>centers</span></a>        <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>({VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                      (len([VV]) = n)} a)] | (len([VV]) &gt; 0)}
 -&gt; {VV : [(GHC.Types.Double)] | (n = len([VV])),(len([VV]) = n)})
-&gt; xs:[{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                            (len([VV]) = n)} a)] | (len([VV]) &gt; 0)}]
-&gt; {VV : [{VV : [(GHC.Types.Double)] | (n = len([VV])),
                                       (len([VV]) = n)}] | (len([VV]) = len([xs]))}</span><span class='hs-varid'>map</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>n:(GHC.Types.Int)
-&gt; {v : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (len([v]) &gt; 0)}
-&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = n)}</span><span class='hs-varid'>clusterCenter</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = n)}</span><span class='hs-varid'>n</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [{v : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (len([v]) &gt; 0)}] | (VV = clusters),
                                                                                                     (len([VV]) &gt;= 0)}</span><span class='hs-varid'>clusters</span></a>
<span class=hs-linenum>190: </span>
<span class=hs-linenum>191: </span>    <span class='hs-comment'>-- 2. Map points to their nearest center</span>
<span class=hs-linenum>192: </span>    <a class=annot href="#"><span class=annottext>[(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                               (len([VV]) = n)} a)]</span><span class='hs-varid'>points</span></a>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[[(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                (len([VV]) = n)} a)]]
-&gt; [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                  (len([VV]) = n)} a)]</span><span class='hs-varid'>concat</span></a> <a class=annot href="#"><span class=annottext>{VV : [{v : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (len([v]) &gt; 0)}] | (VV = clusters),
                                                                                                     (len([VV]) &gt;= 0)}</span><span class='hs-varid'>clusters</span></a>
<span class=hs-linenum>193: </span>    <a class=annot href="#"><span class=annottext>[({VV : [(GHC.Types.Double)] | (n = len([VV])),
                               (len([VV]) = n),
                               (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                 (len([VV]) = n),
                                                                                                 (len([VV]) &gt;= 0)} a))]</span><span class='hs-varid'>centeredPoints</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(GHC.Classes.Ord
  ([GHC.Types.Double], KMeans.WrapType [GHC.Types.Double] a))</span><span class='hs-varid'>sort</span></a> <a class=annot href="#"><span class=annottext>{VV : [({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                     (len([VV]) = n),
                                     (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                       (len([VV]) = n),
                                                                                                       (len([VV]) &gt;= 0)} a))] | (len([VV]) = len([points])),
                                                                                                                                (len([VV]) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>({VV : [(GHC.Types.Double)] | (n = len([VV])),
                              (len([VV]) = n),
                              (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                (len([VV]) = n),
                                                                                                (len([VV]) &gt;= 0)} a))</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>n:(GHC.Types.Int)
-&gt; (KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)
-&gt; [{VV : [(GHC.Types.Double)] | (len([VV]) = n)}]
-&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = n)}</span><span class='hs-varid'>nearestCenter</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = n)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                              (len([VV]) = n)} a)</span><span class='hs-varid'>p</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Double)] | (n = len([VV])),
                                    (len([VV]) = n)}] | (VV = centers),
                                                        (len([VV]) = len([clusters])),
                                                        (len([VV]) &gt;= 0)}</span><span class='hs-varid'>centers</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                              (len([VV]) = n)} a)</span><span class='hs-varid'>p</span></a><span class='hs-layout'>)</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>p</span> <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                     (len([VV]) = n)} a)] | (VV = points),
                                                                            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>points</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>194: </span>
<span class=hs-linenum>195: </span>    <span class='hs-comment'>-- 3. Group points by nearest center to get new clusters</span>
<span class=hs-linenum>196: </span>    <a class=annot href="#"><span class=annottext>[{VV : [({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                      (len([VV]) = n),
                                      (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                        (len([VV]) = n),
                                                                                                        (len([VV]) &gt;= 0)} a))] | (len([VV]) &gt; 0)}]</span><span class='hs-varid'>centeredGroups</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(({VV : [(GHC.Types.Double)] | (n = len([VV])),
                               (len([VV]) = n),
                               (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                 (len([VV]) = n),
                                                                                                 (len([VV]) &gt;= 0)} a))
 -&gt; ({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                  (len([VV]) = n),
                                  (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                    (len([VV]) = n),
                                                                                                    (len([VV]) &gt;= 0)} a))
 -&gt; (GHC.Types.Bool))
-&gt; [({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                  (len([VV]) = n),
                                  (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                    (len([VV]) = n),
                                                                                                    (len([VV]) &gt;= 0)} a))]
-&gt; [{VV : [({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                         (len([VV]) = n),
                                         (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                           (len([VV]) = n),
                                                                                                           (len([VV]) &gt;= 0)} a))] | (len([VV]) &gt; 0)}]</span><span class='hs-varid'>groupBy</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(GHC.Classes.Eq [GHC.Types.Double])</span><span class='hs-layout'>(</span></a><span class='hs-varop'>==</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>({VV : [(GHC.Types.Double)] | (n = len([VV])),
                              (len([VV]) = n),
                              (len([VV]) &gt;= 0)}
 -&gt; {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                 (len([VV]) = n),
                                 (len([VV]) &gt;= 0)}
 -&gt; (GHC.Types.Bool))
-&gt; (({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                  (len([VV]) = n),
                                  (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                    (len([VV]) = n),
                                                                                                    (len([VV]) &gt;= 0)} a))
    -&gt; {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                    (len([VV]) = n),
                                    (len([VV]) &gt;= 0)})
-&gt; ({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                 (len([VV]) = n),
                                 (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                   (len([VV]) = n),
                                                                                                   (len([VV]) &gt;= 0)} a))
-&gt; ({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                 (len([VV]) = n),
                                 (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                   (len([VV]) = n),
                                                                                                   (len([VV]) &gt;= 0)} a))
-&gt; (GHC.Types.Bool)</span><span class='hs-varop'>`on`</span></a> <a class=annot href="#"><span class=annottext>({VV : [(GHC.Types.Double)] | (n = len([VV])),
                              (len([VV]) = n),
                              (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                (len([VV]) = n),
                                                                                                (len([VV]) &gt;= 0)} a))
-&gt; {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                (len([VV]) = n),
                                (len([VV]) &gt;= 0)}</span><span class='hs-varid'>fst</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                     (len([VV]) = n),
                                     (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                       (len([VV]) = n),
                                                                                                       (len([VV]) &gt;= 0)} a))] | (VV = centeredPoints),
                                                                                                                                (len([VV]) &gt;= 0)}</span><span class='hs-varid'>centeredPoints</span></a>
<span class=hs-linenum>197: </span>    <a class=annot href="#"><span class=annottext>{VV : [{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                            (len([VV]) = n),
                                                            (len([VV]) &gt;= 0)} a)] | (len([VV]) &gt; 0)}] | (len([VV]) = len([centeredGroups]))}</span><span class='hs-varid'>clusters'</span></a>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>({VV : [({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                      (len([VV]) = n),
                                      (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                        (len([VV]) = n),
                                                                                                        (len([VV]) &gt;= 0)} a))] | (len([VV]) &gt; 0)}
 -&gt; {VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                         (len([VV]) = n),
                                                         (len([VV]) &gt;= 0)} a)] | (len([VV]) &gt; 0)})
-&gt; xs:[{VV : [({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                            (len([VV]) = n),
                                            (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                              (len([VV]) = n),
                                                                                                              (len([VV]) &gt;= 0)} a))] | (len([VV]) &gt; 0)}]
-&gt; {VV : [{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                               (len([VV]) = n),
                                                               (len([VV]) &gt;= 0)} a)] | (len([VV]) &gt; 0)}] | (len([VV]) = len([xs]))}</span><span class='hs-varid'>map</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(({VV : [(GHC.Types.Double)] | (n = len([VV])),
                               (len([VV]) = n),
                               (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                 (len([VV]) = n),
                                                                                                 (len([VV]) &gt;= 0)} a))
 -&gt; (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                  (len([VV]) = n),
                                                  (len([VV]) &gt;= 0)} a))
-&gt; xs:[({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                     (len([VV]) = n),
                                     (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                       (len([VV]) = n),
                                                                                                       (len([VV]) &gt;= 0)} a))]
-&gt; {VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                        (len([VV]) = n),
                                                        (len([VV]) &gt;= 0)} a)] | (len([VV]) = len([xs]))}</span><span class='hs-varid'>map</span></a> <a class=annot href="#"><span class=annottext>({VV : [(GHC.Types.Double)] | (n = len([VV])),
                              (len([VV]) = n),
                              (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                (len([VV]) = n),
                                                                                                (len([VV]) &gt;= 0)} a))
-&gt; (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                 (len([VV]) = n),
                                                 (len([VV]) &gt;= 0)} a)</span><span class='hs-varid'>snd</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                            (len([VV]) = n),
                                            (len([VV]) &gt;= 0)} , (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                                                                              (len([VV]) = n),
                                                                                                              (len([VV]) &gt;= 0)} a))] | (len([VV]) &gt; 0)}] | (VV = centeredGroups),
                                                                                                                                                           (len([VV]) &gt;= 0)}</span><span class='hs-varid'>centeredGroups</span></a>
</pre>

The behavior of `refineCluster` is pithily captured by its type


<pre><span class=hs-linenum>203: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>refineCluster</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span>
<span class=hs-linenum>204: </span>                  <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Clustering</span> <span class='hs-layout'>(</span><span class='hs-conid'>GenPoint</span> <span class='hs-varid'>a</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span>
<span class=hs-linenum>205: </span>                  <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Clustering</span> <span class='hs-layout'>(</span><span class='hs-conid'>GenPoint</span> <span class='hs-varid'>a</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>

The refined clustering is computed in three steps.

1. First, we compute the `centers :: [(Point n)]` of the current `clusters`.
   This is achieved by using `clusterCenter`, which maps a list of generalized
   `n`-dimensional points to a *single* `n` dimensional point (i.e. `Point n`).

2. Next, we pair each point `p` in the list of all `points` with its `nearestCenter`.

3. Finally, the pairs in the list of `centeredPoints` are grouped by the
   center, i.e. the first element of the tuple. The resulting groups are
   projected back to the original generalized points yielding the new
   clustering.

 The type of the output follows directly from
<pre><span class=hs-linenum>222: </span><span class='hs-definition'>groupBy</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Clustering</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
</pre>

from [last time][kmeansI]. At the call site above, LiquidHaskell infers that
`a` can be instantiated with `((Point n), (GenPoint a n))` thereby establishing
that, after *projecting away* the first element, the output is a list of
non-empty lists of generalized `n`-dimensional points.

That leaves us with the two crucial bits of the algorithm: `clusterCenter`
and `nearestCenter`.

Computing the Center of a Cluster
---------------------------------

The center of an `n`-dimensional cluster is simply an `n`-dimensional point
whose value in each dimension is equal to the *average* value of that
dimension across all the points in the cluster.

 For example, consider a cluster of 2-dimensional points,
<pre><span class=hs-linenum>241: </span><span class='hs-definition'>exampleCluster</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span> <span class='hs-keyglyph'>[</span><span class='hs-num'>0</span><span class='hs-layout'>,</span>  <span class='hs-num'>0</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>242: </span>                 <span class='hs-layout'>,</span> <span class='hs-keyglyph'>[</span><span class='hs-num'>1</span><span class='hs-layout'>,</span> <span class='hs-num'>10</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>243: </span>                 <span class='hs-layout'>,</span> <span class='hs-keyglyph'>[</span><span class='hs-num'>2</span><span class='hs-layout'>,</span> <span class='hs-num'>20</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>244: </span>                 <span class='hs-layout'>,</span> <span class='hs-keyglyph'>[</span><span class='hs-num'>4</span><span class='hs-layout'>,</span> <span class='hs-num'>40</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>245: </span>                 <span class='hs-layout'>,</span> <span class='hs-keyglyph'>[</span><span class='hs-num'>5</span><span class='hs-layout'>,</span> <span class='hs-num'>50</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>]</span>
</pre>

 The center of the cluster is
<pre><span class=hs-linenum>249: </span><span class='hs-definition'>exampleCenter</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span> <span class='hs-layout'>(</span><span class='hs-num'>0</span> <span class='hs-varop'>+</span> <span class='hs-num'>1</span>  <span class='hs-varop'>+</span> <span class='hs-num'>2</span>  <span class='hs-varop'>+</span> <span class='hs-num'>4</span>  <span class='hs-varop'>+</span> <span class='hs-num'>5</span> <span class='hs-layout'>)</span> <span class='hs-varop'>/</span> <span class='hs-num'>5</span>
<span class=hs-linenum>250: </span>                <span class='hs-layout'>,</span> <span class='hs-layout'>(</span><span class='hs-num'>0</span> <span class='hs-varop'>+</span> <span class='hs-num'>10</span> <span class='hs-varop'>+</span> <span class='hs-num'>20</span> <span class='hs-varop'>+</span> <span class='hs-num'>40</span> <span class='hs-varop'>+</span> <span class='hs-num'>50</span><span class='hs-layout'>)</span> <span class='hs-varop'>/</span> <span class='hs-num'>5</span> <span class='hs-keyglyph'>]</span>
</pre>

 which is just
<pre><span class=hs-linenum>254: </span><span class='hs-definition'>exampleCenter</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span> <span class='hs-num'>3</span><span class='hs-layout'>,</span> <span class='hs-num'>30</span> <span class='hs-keyglyph'>]</span>
</pre>

Thus, we can compute a `clusterCenter` via the following procedure


<pre><span class=hs-linenum>260: </span><a class=annot href="#"><span class=annottext>n:(GHC.Types.Int)
-&gt; {v : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (len([v]) &gt; 0)}
-&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = n)}</span><span class='hs-definition'>clusterCenter</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>{v : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (len([v]) &gt; 0)}</span><span class='hs-varid'>xs</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>({VV : [(GHC.Types.Double)] | (numPoints = len([VV])),
                              (len([VV]) = numPoints),
                              (len([VV]) = len([xs])),
                              (len([VV]) &gt; 0)}
 -&gt; (GHC.Types.Double))
-&gt; xs:[{VV : [(GHC.Types.Double)] | (numPoints = len([VV])),
                                    (len([VV]) = numPoints),
                                    (len([VV]) = len([xs])),
                                    (len([VV]) &gt; 0)}]
-&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = len([xs]))}</span><span class='hs-varid'>map</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Double)] | (numPoints = len([VV])),
                             (len([VV]) = numPoints),
                             (len([VV]) = len([xs])),
                             (len([VV]) &gt; 0)}
-&gt; (GHC.Types.Double)</span><span class='hs-varid'>average</span></a> <a class=annot href="#"><span class=annottext>{v : [{VV : [(GHC.Types.Double)] | (len([VV]) = numPoints)}] | (v = xs'),
                                                               (len([v]) = n),
                                                               (len([v]) &gt;= 0)}</span><span class='hs-varid'>xs'</span></a>
<span class=hs-linenum>261: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>262: </span>    <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = len([xs]))}</span><span class='hs-varid'>numPoints</span></a>      <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>xs:[(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                  (len([VV]) = n)} a)]
-&gt; {VV : (GHC.Types.Int) | (VV = len([xs]))}</span><span class='hs-varid'>length</span></a> <a class=annot href="#"><span class=annottext>{v : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (v = xs),
                                                                           (len([v]) &gt; 0),
                                                                           (len([v]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
<span class=hs-linenum>263: </span>    <a class=annot href="#"><span class=annottext>{v : [{VV : [(GHC.Types.Double)] | (len([VV]) = numPoints)}] | (len([v]) = n)}</span><span class='hs-varid'>xs'</span></a>            <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>c:(GHC.Types.Int)
-&gt; r:{VV : (GHC.Types.Int) | (VV &gt; 0)}
-&gt; {v : [{VV : [(GHC.Types.Double)] | (len([VV]) = c)}] | (len([v]) = r)}
-&gt; {v : [{VV : [(GHC.Types.Double)] | (len([VV]) = r)}] | (len([v]) = c)}</span><span class='hs-varid'>transpose</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = n)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = numPoints),(VV = len([xs]))}</span><span class='hs-varid'>numPoints</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>((KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                               (len([VV]) = n)} a)
 -&gt; {VV : [(GHC.Types.Double)] | (n = len([VV])),(len([VV]) = n)})
-&gt; xs:[(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                     (len([VV]) = n)} a)]
-&gt; {VV : [{VV : [(GHC.Types.Double)] | (n = len([VV])),
                                       (len([VV]) = n)}] | (len([VV]) = len([xs]))}</span><span class='hs-varid'>map</span></a> <a class=annot href="#"><span class=annottext>(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                              (len([VV]) = n)} a)
-&gt; {VV : [(GHC.Types.Double)] | (n = len([VV])),(len([VV]) = n)}</span><span class='hs-varid'>getVect</span></a> <a class=annot href="#"><span class=annottext>{v : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (v = xs),
                                                                           (len([v]) &gt; 0),
                                                                           (len([v]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>264: </span>
<span class=hs-linenum>265: </span>    <span class='hs-varid'>average</span>        <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Double</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Double</span>
<span class=hs-linenum>266: </span>    <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Double)] | (numPoints = len([VV])),
                             (len([VV]) = numPoints),
                             (len([VV]) = len([xs])),
                             (len([VV]) &gt; 0)}
-&gt; (GHC.Types.Double)</span><span class='hs-varid'>average</span></a>        <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(GHC.Types.Double)
-&gt; {VV : (GHC.Types.Int) | (VV &gt; 0)} -&gt; (GHC.Types.Double)</span><span class='hs-varop'>`safeDiv`</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = numPoints),(VV = len([xs]))}</span><span class='hs-varid'>numPoints</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>((GHC.Types.Double) -&gt; (GHC.Types.Double))
-&gt; ({VV : [(GHC.Types.Double)] | (numPoints = len([VV])),
                                 (len([VV]) = numPoints),
                                 (len([VV]) = len([xs])),
                                 (len([VV]) &gt; 0)}
    -&gt; (GHC.Types.Double))
-&gt; {VV : [(GHC.Types.Double)] | (numPoints = len([VV])),
                                (len([VV]) = numPoints),
                                (len([VV]) = len([xs])),
                                (len([VV]) &gt; 0)}
-&gt; (GHC.Types.Double)</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>[(GHC.Types.Double)] -&gt; (GHC.Types.Double)</span><span class='hs-varid'>sum</span></a>
</pre>

First, we `transpose` the matrix of points in the cluster.
Suppose that `xs` is the `exampleCluster` from above
(and so `n` is `2` and `numPoints` is `5`.)

 In this scenario, `xs'` is
<pre><span class=hs-linenum>274: </span><span class='hs-definition'>xs'</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span> <span class='hs-keyglyph'>[</span><span class='hs-num'>0</span><span class='hs-layout'>,</span>  <span class='hs-num'>1</span><span class='hs-layout'>,</span>  <span class='hs-num'>2</span><span class='hs-layout'>,</span>  <span class='hs-num'>4</span><span class='hs-layout'>,</span>  <span class='hs-num'>5</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>275: </span>      <span class='hs-layout'>,</span> <span class='hs-keyglyph'>[</span><span class='hs-num'>0</span><span class='hs-layout'>,</span> <span class='hs-num'>10</span><span class='hs-layout'>,</span> <span class='hs-num'>20</span><span class='hs-layout'>,</span> <span class='hs-num'>40</span><span class='hs-layout'>,</span> <span class='hs-num'>50</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>]</span>
</pre>

and so `map average xs'` evaluates to `exampleCenter` from above.

We have ensured that the division in the average does not lead to
any nasty surprises via a *safe division* function whose precondition
checks that the denominator is non-zero, [as illustrated here][ref101].


<pre><span class=hs-linenum>285: </span><span class='hs-comment'>{- safeDiv   :: (Fractional a) =&gt; a -&gt; {v:Int | v != 0} -&gt; a -}</span>
<span class=hs-linenum>286: </span><span class='hs-definition'>safeDiv</span>     <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Fractional</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>287: </span><a class=annot href="#"><span class=annottext>(GHC.Real.Fractional a)
-&gt; a -&gt; {VV : (GHC.Types.Int) | (VV &gt; 0)} -&gt; a</span><span class='hs-definition'>safeDiv</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>n</span></a> <span class='hs-num'>0</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | false} -&gt; {VV : a | false}</span><span class='hs-varid'>liquidError</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"divide by zero"</span></a>
<span class=hs-linenum>288: </span><span class='hs-definition'>safeDiv</span> <span class='hs-varid'>n</span> <span class='hs-varid'>d</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = n)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x:a -&gt; y:{VV : a | (VV != 0)} -&gt; {VV : a | (VV = (x / y))}</span><span class='hs-varop'>/</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(GHC.Num.Num a)</span><span class='hs-varid'>fromIntegral</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt; 0)}</span><span class='hs-varid'>d</span></a><span class='hs-layout'>)</span>
</pre>

LiquidHaskell verifies that the divide-by-zero never occurs, and furthermore,
that `clusterCenter` indeed computes an `n`-dimensional center by inferring that


<pre><span class=hs-linenum>295: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>clusterCenter</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>NonEmptyList</span> <span class='hs-layout'>(</span><span class='hs-conid'>GenPoint</span> <span class='hs-varid'>a</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Point</span> <span class='hs-varid'>n</span> <span class='hs-keyword'>@-}</span>
</pre>

LiquidHaskell deduces that the *input* list of points `xs` is non-empty
from the fact that `clusterCenter` is only invoked on the elements of a
`Clustering` which comprise only non-empty lists. Since `xs` is non-empty,
i.e. `(len xs) > 0`, LiquidHaskell infers that `numPoints` is positive
(hover over `length` to understand why), and hence, LiquidHaskell is
satisfied that the call to `safeDiv` will always proceed without any
incident.

 To establish the *output* type `Point n` LiquidHaskell leans on the fact that
<pre><span class=hs-linenum>307: </span><span class='hs-definition'>transpose</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>m</span><span class='hs-conop'>:</span><span class='hs-conid'>PosInt</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Matrix</span> <span class='hs-varid'>a</span> <span class='hs-varid'>m</span> <span class='hs-varid'>n</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Matrix</span> <span class='hs-varid'>a</span> <span class='hs-varid'>n</span> <span class='hs-varid'>m</span>
</pre>

to deduce that `xs'` is of type `Matrix Double n numPoints`, that is to
say, a list of length `n` containing lists of length `numPoints`. Since
`map` preserves the length, the value `map average xs'` is also a list
of length `n`, i.e. `Point n`.


Finding the Nearest Center
--------------------------

The last piece of the puzzle is `nearestCenter` which maps each
(generalized) point to the center that it is nearest. The code is
pretty self-explanatory:


<pre><span class=hs-linenum>324: </span><span class='hs-definition'>nearestCenter</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>WrapType</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Double</span><span class='hs-keyglyph'>]</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>Double</span><span class='hs-keyglyph'>]</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Double</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>325: </span><a class=annot href="#"><span class=annottext>n:(GHC.Types.Int)
-&gt; (KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)
-&gt; [{VV : [(GHC.Types.Double)] | (len([VV]) = n)}]
-&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = n)}</span><span class='hs-definition'>nearestCenter</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                     (len([VV]) = n),
                                     (len([VV]) &gt;= 0)} , (GHC.Types.Double))] | (len([VV]) &gt;= 0)}
-&gt; {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                (len([VV]) = n),
                                (len([VV]) &gt;= 0)}</span><span class='hs-varid'>minKey</span></a> <a class=annot href="#"><span class=annottext>({VV : [({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                      (len([VV]) = n),
                                      (len([VV]) &gt;= 0)} , (GHC.Types.Double))] | (len([VV]) &gt;= 0)}
 -&gt; {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                 (len([VV]) = n),
                                 (len([VV]) &gt;= 0)})
-&gt; ([{VV : [(GHC.Types.Double)] | (n = len([VV])),(len([VV]) = n)}]
    -&gt; {VV : [({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                            (len([VV]) = n),
                                            (len([VV]) &gt;= 0)} , (GHC.Types.Double))] | (len([VV]) &gt;= 0)})
-&gt; [{VV : [(GHC.Types.Double)] | (n = len([VV])),(len([VV]) = n)}]
-&gt; {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                (len([VV]) = n),
                                (len([VV]) &gt;= 0)}</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>({VV : [(GHC.Types.Double)] | (n = len([VV])),(len([VV]) = n)}
 -&gt; ({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                  (len([VV]) = n),
                                  (len([VV]) &gt;= 0)} , (GHC.Types.Double)))
-&gt; xs:[{VV : [(GHC.Types.Double)] | (n = len([VV])),
                                    (len([VV]) = n)}]
-&gt; {VV : [({VV : [(GHC.Types.Double)] | (n = len([VV])),
                                        (len([VV]) = n),
                                        (len([VV]) &gt;= 0)} , (GHC.Types.Double))] | (len([VV]) = len([xs]))}</span><span class='hs-varid'>map</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>c:{VV : [(GHC.Types.Double)] | (n = len([VV])),(len([VV]) = n)}
-&gt; ({VV : [(GHC.Types.Double)] | (VV = c),
                                 (n = len([VV])),
                                 (len([VV]) = n),
                                 (len([VV]) = len([c])),
                                 (len([VV]) &gt;= 0)} , (GHC.Types.Double))</span><span class='hs-keyglyph'>\</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Double)] | (n = len([VV])),(len([VV]) = n)}</span><span class='hs-varid'>c</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>x1:a -&gt; b -&gt; (a , b)</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Double)] | (VV = c),
                             (n = len([VV])),
                             (len([VV]) = n),
                             (len([VV]) &gt;= 0)}</span><span class='hs-varid'>c</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>a:{VV : [(GHC.Types.Double)] | (len([VV]) &gt;= 0)}
-&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = len([a])),
                                (len([VV]) &gt;= 0)}
-&gt; (GHC.Types.Double)</span><span class='hs-varid'>distance</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Double)] | (VV = c),
                             (n = len([VV])),
                             (len([VV]) = n),
                             (len([VV]) &gt;= 0)}</span><span class='hs-varid'>c</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                              (len([VV]) = n),
                                              (len([VV]) = len([c])),
                                              (len([VV]) &gt;= 0)} a)
-&gt; {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                (len([VV]) = n),
                                (len([VV]) = len([c])),
                                (len([VV]) &gt;= 0)}</span><span class='hs-varid'>getVect</span></a> <a class=annot href="#"><span class=annottext>{VV : (KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a) | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
</pre>

We `map` the centers to a tuple of center `c` and the `distance` between
`x` and `c`, and then we select the tuple with the smallest distance


<pre><span class=hs-linenum>332: </span><span class='hs-definition'>minKey</span>  <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-varid'>k</span><span class='hs-layout'>,</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>k</span>
<span class=hs-linenum>333: </span><a class=annot href="#"><span class=annottext>(GHC.Classes.Ord a) -&gt; {VV : [(b , a)] | (len([VV]) &gt;= 0)} -&gt; b</span><span class='hs-definition'>minKey</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(a , b) -&gt; a</span><span class='hs-varid'>fst</span></a> <a class=annot href="#"><span class=annottext>((a , b) -&gt; a)
-&gt; ({VV : [(a , b)] | (len([VV]) &gt;= 0)} -&gt; (a , b))
-&gt; {VV : [(a , b)] | (len([VV]) &gt;= 0)}
-&gt; a</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>((a , b) -&gt; (a , b) -&gt; (GHC.Types.Ordering))
-&gt; [(a , b)] -&gt; (a , b)</span><span class='hs-varid'>minimumBy</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(a , b) -&gt; (a , b) -&gt; (GHC.Types.Ordering)</span><span class='hs-keyglyph'>\</span></a><a class=annot href="#"><span class=annottext>(a , b)</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>(a , b)</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>x:a
-&gt; y:a
-&gt; {VV : (GHC.Types.Ordering) | ((VV = EQ) &lt;=&gt; (x = y)),
                                ((VV = GT) &lt;=&gt; (x &gt; y)),
                                ((VV = LT) &lt;=&gt; (x &lt; y))}</span><span class='hs-varid'>compare</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(a , b) -&gt; b</span><span class='hs-varid'>snd</span></a> <a class=annot href="#"><span class=annottext>{VV : (a , b) | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(a , b) -&gt; b</span><span class='hs-varid'>snd</span></a> <a class=annot href="#"><span class=annottext>{VV : (a , b) | (VV = y)}</span><span class='hs-varid'>y</span></a><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
</pre>

The interesting bit is that the `distance` function uses `zipWith` to
ensure that the dimensionality of the center and the point match up.


<pre><span class=hs-linenum>340: </span><span class='hs-definition'>distance</span>     <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Double</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Double</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Double</span>
<span class=hs-linenum>341: </span><a class=annot href="#"><span class=annottext>a:{VV : [(GHC.Types.Double)] | (len([VV]) &gt;= 0)}
-&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = len([a])),
                                (len([VV]) &gt;= 0)}
-&gt; (GHC.Types.Double)</span><span class='hs-definition'>distance</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Double)] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Double)] | (len([VV]) = len([a])),
                             (len([VV]) &gt;= 0)}</span><span class='hs-varid'>b</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(GHC.Types.Double) -&gt; (GHC.Types.Double)</span><span class='hs-varid'>sqrt</span></a> <a class=annot href="#"><span class=annottext>((GHC.Types.Double) -&gt; (GHC.Types.Double))
-&gt; ({VV : [(GHC.Types.Double)] | (len([VV]) = len([a])),
                                 (len([VV]) = len([b])),
                                 (len([VV]) &gt;= 0)}
    -&gt; (GHC.Types.Double))
-&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = len([a])),
                                (len([VV]) = len([b])),
                                (len([VV]) &gt;= 0)}
-&gt; (GHC.Types.Double)</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>[(GHC.Types.Double)] -&gt; (GHC.Types.Double)</span><span class='hs-varid'>sum</span></a> <a class=annot href="#"><span class=annottext>({VV : [(GHC.Types.Double)] | (len([VV]) = len([a])),
                              (len([VV]) = len([b])),
                              (len([VV]) &gt;= 0)}
 -&gt; (GHC.Types.Double))
-&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = len([a])),
                                (len([VV]) = len([b])),
                                (len([VV]) &gt;= 0)}
-&gt; (GHC.Types.Double)</span><span class='hs-varop'>$</span></a> <a class=annot href="#"><span class=annottext>((GHC.Types.Double) -&gt; (GHC.Types.Double) -&gt; (GHC.Types.Double))
-&gt; xs:[(GHC.Types.Double)]
-&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = len([xs]))}
-&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = len([xs]))}</span><span class='hs-varid'>zipWith</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(GHC.Types.Double) -&gt; (GHC.Types.Double) -&gt; (GHC.Types.Double)</span><span class='hs-keyglyph'>\</span></a><a class=annot href="#"><span class=annottext>(GHC.Types.Double)</span><span class='hs-varid'>v1</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Double)</span><span class='hs-varid'>v2</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Integer.Type.Integer) | (VV = 2)}</span><span class='hs-layout'>(</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Double) | (VV = v1)}</span><span class='hs-varid'>v1</span></a> <a class=annot href="#"><span class=annottext>x:(GHC.Types.Double)
-&gt; y:(GHC.Types.Double)
-&gt; {VV : (GHC.Types.Double) | (VV = (x - y))}</span><span class='hs-comment'>-</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Double) | (VV = v2)}</span><span class='hs-varid'>v2</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>(GHC.Types.Double)
-&gt; (GHC.Integer.Type.Integer) -&gt; (GHC.Types.Double)</span><span class='hs-varop'>^</span></a> <span class='hs-num'>2</span><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Double)] | (VV = a),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Double)] | (VV = b),
                             (len([VV]) = len([a])),
                             (len([VV]) &gt;= 0)}</span><span class='hs-varid'>b</span></a>
</pre>

LiquidHaskell verifies `distance` by inferring that


<pre><span class=hs-linenum>347: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>nearestCenter</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>GenPoint</span> <span class='hs-varid'>a</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-conid'>Point</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Point</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>

First, LiquidHaskell deduces that each center in `cs` is indeed `n`-dimensional, which
follows from the output type of `clusterCenter`. Since `x` is a `(GenPoint a n)`
LiquidHaskell infers that both `c` and `getVect x` are of an equal length `n`.

 Consequently, the call to
<pre><span class=hs-linenum>355: </span><span class='hs-definition'>zipWith</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>c</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>List</span> <span class='hs-varid'>b</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>List</span> <span class='hs-varid'>c</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
</pre>

[discussed last time][kmeansI] is determined to be safe.

Finally, the value returned is just one of the input centers and so is a `(Point n)`.


Putting It All Together: Top-Level API
--------------------------------------

We can bundle the algorithm into two top-level API functions.

First, a version that clusters *generalized* points. In this case, we
require a function that can `project` an `a` value to an `n`-dimensional
point. This function just wraps each `a`, clusters via `kmeans'` and then
unwraps the points.


<pre><span class=hs-linenum>374: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>kmeansGen</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span>
<span class=hs-linenum>375: </span>              <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Point</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>376: </span>              <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>k</span><span class='hs-conop'>:</span><span class='hs-conid'>PosInt</span>
<span class=hs-linenum>377: </span>              <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>378: </span>              <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Clustering</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
<span class=hs-linenum>379: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>380: </span>
<span class=hs-linenum>381: </span><a class=annot href="#"><span class=annottext>n:(GHC.Types.Int)
-&gt; (a -&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = n)})
-&gt; {VV : (GHC.Types.Int) | (VV &gt; 0)}
-&gt; [a]
-&gt; [{VV : [a] | (len([VV]) &gt; 0)}]</span><span class='hs-definition'>kmeansGen</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>a -&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = n)}</span><span class='hs-varid'>project</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt; 0)}</span><span class='hs-varid'>k</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>({VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                      (len([VV]) = n)} a)] | (len([VV]) &gt; 0)}
 -&gt; {VV : [a] | (len([VV]) &gt; 0)})
-&gt; xs:[{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                            (len([VV]) = n)} a)] | (len([VV]) &gt; 0)}]
-&gt; {VV : [{VV : [a] | (len([VV]) &gt; 0)}] | (len([VV]) = len([xs]))}</span><span class='hs-varid'>map</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>((KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                               (len([VV]) = n)} a)
 -&gt; a)
-&gt; xs:[(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                     (len([VV]) = n)} a)]
-&gt; {VV : [a] | (len([VV]) = len([xs]))}</span><span class='hs-varid'>map</span></a> <a class=annot href="#"><span class=annottext>(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                              (len([VV]) = n)} a)
-&gt; a</span><span class='hs-varid'>getVal</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>382: </span>                      <a class=annot href="#"><span class=annottext>([{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                       (len([VV]) = n)} a)] | (len([VV]) &gt; 0)}]
 -&gt; {VV : [{VV : [a] | (len([VV]) &gt; 0)}] | (len([VV]) &gt;= 0)})
-&gt; ([a]
    -&gt; [{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                             (len([VV]) = n)} a)] | (len([VV]) &gt; 0)}])
-&gt; [a]
-&gt; {VV : [{VV : [a] | (len([VV]) &gt; 0)}] | (len([VV]) &gt;= 0)}</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>n:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV &gt; 0)}
-&gt; [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)]
-&gt; [{v : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (len([VV]) = n)} a)] | (len([v]) &gt; 0)}]</span><span class='hs-varid'>kmeans'</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = n)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = k),(VV &gt; 0)}</span><span class='hs-varid'>k</span></a>
<span class=hs-linenum>383: </span>                      <a class=annot href="#"><span class=annottext>({VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                      (len([VV]) = n),
                                                      (len([VV]) &gt;= 0)} a)] | (len([VV]) &gt;= 0)}
 -&gt; [{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                          (len([VV]) = n)} a)] | (len([VV]) &gt; 0)}])
-&gt; ([a]
    -&gt; {VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                            (len([VV]) = n),
                                                            (len([VV]) &gt;= 0)} a)] | (len([VV]) &gt;= 0)})
-&gt; [a]
-&gt; [{VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                         (len([VV]) = n)} a)] | (len([VV]) &gt; 0)}]</span><span class='hs-varop'>.</span></a> <a class=annot href="#"><span class=annottext>(a
 -&gt; (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                  (len([VV]) = n),
                                                  (len([VV]) &gt;= 0)} a))
-&gt; xs:[a]
-&gt; {VV : [(KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                        (len([VV]) = n),
                                                        (len([VV]) &gt;= 0)} a)] | (len([VV]) = len([xs]))}</span><span class='hs-varid'>map</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x:a
-&gt; (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                 (len([VV]) = n),
                                                 (len([VV]) &gt;= 0)} {VV : a | (VV = x)})</span><span class='hs-keyglyph'>\</span></a><a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Double)] | (n = len([VV])),
                             (len([VV]) = n),
                             (len([VV]) &gt;= 0)}
-&gt; {VV : a | (VV = x)}
-&gt; (KMeans.WrapType {VV : [(GHC.Types.Double)] | (n = len([VV])),
                                                 (len([VV]) = n),
                                                 (len([VV]) &gt;= 0)} {VV : a | (VV = x)})</span><span class='hs-conid'>WrapType</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>a -&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = n)}</span><span class='hs-varid'>project</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span>
</pre>

Second, a specialized version that operates directly on `n`-dimensional
points. The specialized version just calls the general version with a
trivial `id` projection.


<pre><span class=hs-linenum>391: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>kmeans</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span>
<span class=hs-linenum>392: </span>           <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>k</span><span class='hs-conop'>:</span><span class='hs-conid'>PosInt</span>
<span class=hs-linenum>393: </span>           <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>points</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-conid'>Point</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>394: </span>           <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Clustering</span> <span class='hs-layout'>(</span><span class='hs-conid'>Point</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>395: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>396: </span>
<span class=hs-linenum>397: </span><a class=annot href="#"><span class=annottext>n:(GHC.Types.Int)
-&gt; {VV : (GHC.Types.Int) | (VV &gt; 0)}
-&gt; [{VV : [(GHC.Types.Double)] | (len([VV]) = n)}]
-&gt; [{v : [{VV : [(GHC.Types.Double)] | (len([VV]) = n)}] | (len([v]) &gt; 0)}]</span><span class='hs-definition'>kmeans</span></a> <a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>n</span></a>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>n:(GHC.Types.Int)
-&gt; ({VV : [(GHC.Types.Double)] | (n = len([VV])),(len([VV]) = n)}
    -&gt; {VV : [(GHC.Types.Double)] | (len([VV]) = n)})
-&gt; {VV : (GHC.Types.Int) | (VV &gt; 0)}
-&gt; [{VV : [(GHC.Types.Double)] | (n = len([VV])),(len([VV]) = n)}]
-&gt; [{VV : [{VV : [(GHC.Types.Double)] | (n = len([VV])),
                                        (len([VV]) = n)}] | (len([VV]) &gt; 0)}]</span><span class='hs-varid'>kmeansGen</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = n)}</span><span class='hs-varid'>n</span></a> <a class=annot href="#"><span class=annottext>x:{VV : [(GHC.Types.Double)] | (n = len([VV])),(len([VV]) = n)}
-&gt; {VV : [(GHC.Types.Double)] | (VV = x),
                                (n = len([VV])),
                                (len([VV]) = n)}</span><span class='hs-varid'>id</span></a>
</pre>

Conclusions
-----------

I hope that over the last two posts you have gotten a sense of

1. What KMeans clustering is all about,

2. How measures and refinements can be used to describe the behavior
   of common list operations like `map`, `transpose`, `groupBy`, `zipWith`, and so on,

3. How LiquidHaskell's automated inference makes it easy to write and
   verify invariants of non-trivial programs.

The sharp reader will have noticed that the one *major*, non syntactic, change to the
[original code][URL-kmeans] is the addition of the dimension parameter `n` throughout
the code. This is critically required so that we can specify the relevant
invariants (which are in terms of `n`.) The value is actually a ghost, and
never ever used. Fortunately, Haskell's laziness means that we don't have
to worry about it (or other ghost variables) imposing any run-time overhead
at all.

**Exercise:** Incidentally, if you have followed thus far I would
encourage you to ponder about how you might modify the types (and
implementation) to verify that KMeans indeed produces at most `k` clusters...

[ref101]:        /blog/2013/01/01/refinement-types-101.lhs/
[safeList]:      /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/
[kmeansI]:       /blog/2013/02/16/kmeans-clustering-I.lhs/
[kmeansII]:      /blog/2013/02/17/kmeans-clustering-II.lhs/
[URL-take]:      https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/List.lhs#L334
[URL-groupBy]:   http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-List.html#v:groupBy
[URL-transpose]: http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#transpose
[maru]:          http://www.youtube.com/watch?v=8uDuls5TyNE
[demo]:          http://goto.ucsd.edu/~rjhala/liquid/haskell/demo/#?demo=KMeansHelper.hs
[URL-kmeans]:    http://hackage.haskell.org/package/kmeans


