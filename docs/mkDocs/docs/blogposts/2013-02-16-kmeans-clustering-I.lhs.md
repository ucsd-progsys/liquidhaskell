---
layout: post
title: KMeans Clustering I
date: 2013-02-16 16:12
author: Ranjit Jhala
published: true
comments: true
tags:
   - basic
   - measures
demo: KMeansHelper.hs
---

[Last time][safeList] we introduced a new specification mechanism called a
*measure* and demonstrated how to use it to encode the *length* of a list.
We saw how measures could be used to verify that functions like `head` and
`tail` were only called with non-empty lists (whose length was strictly
positive). As several folks pointed out, once LiquidHaskell can reason about
lengths, it can do a lot more than just analyze non-emptiness.

Indeed!

Over the next *two* posts, lets see how one might implement a Kmeans
algorithm that clusters `n`-dimensional points groups, and how LiquidHaskell
can help us write and enforce various dimensionality invariants along the way.

<!-- more -->

<!-- For example, XXX pointed out that we can use the type system to give an *upper* bound on the size of a list, e.g. using lists
     upper bounded by a gigantic `MAX_INT` value as a proxy for finite lists. -->



<pre><span class=hs-linenum>33: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>KMeansHelper</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>34: </span>
<span class=hs-linenum>35: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Prelude</span>                          <span class='hs-varid'>hiding</span>  <span class='hs-layout'>(</span><span class='hs-varid'>zipWith</span><span class='hs-layout'>)</span>
<span class=hs-linenum>36: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>List</span>                                <span class='hs-layout'>(</span><span class='hs-varid'>span</span><span class='hs-layout'>)</span>
<span class=hs-linenum>37: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span>          <span class='hs-layout'>(</span><span class='hs-varid'>liquidError</span><span class='hs-layout'>)</span>
</pre>

Rather than reinvent the wheel, we will modify an existing implementation
of K-Means, [available on hackage][URL-kmeans]. This may not be the
most efficient implementation, but its a nice introduction to the algorithm,
and the general invariants will hold for more sophisticated implementations.

We have broken this entry into two convenient, bite-sized chunks:

+ **Part I**  Introduces the basic types and list operations needed by KMeans,

+ **Part II** Describes how the operations are used in the KMeans implementation.

The Game: Clustering Points
---------------------------

The goal of [K-Means clustering](http://en.wikipedia.org/wiki/K-means_clustering)
is the following. Given

- **Input** : A set of *points* represented by *n-dimensional points*
  in *Euclidian* space, return

- **Output** : A partitioning of the points, into K clusters, in a manner that
  minimizes sum of distances between each point and its cluster center.


The Players: Types
------------------

Lets make matters concrete by creating types for the different elements of the algorithm.

**1. Fixed-Length Lists**  We will represent n-dimensional points using
good old Haskell lists, refined with a predicate that describes the
dimensionality (i.e. length.) To simplify matters, lets package this
into a *type alias* that denotes lists of a given length `N`.


<pre><span class=hs-linenum>75: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>N</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

**2. Points** Next, we can represent an `N`-dimensional point as list of `Double` of length `N`,


<pre><span class=hs-linenum>81: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>Point</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>List</span> <span class='hs-conid'>Double</span> <span class='hs-conid'>N</span> <span class='hs-keyword'>@-}</span>
</pre>

**3. Clusters** A cluster is a **non-empty** list of points,


<pre><span class=hs-linenum>87: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>NonEmptyList</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-varop'>&gt;</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

**4. Clustering** And finally, a clustering is a list of (non-empty) clusters.


<pre><span class=hs-linenum>93: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>Clustering</span> <span class='hs-varid'>a</span>  <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>(</span><span class='hs-conid'>NonEmptyList</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
</pre>

**Notation:** When defining refinement type aliases, we use uppercase variables like `N`
to distinguish value- parameters from the lowercase type parameters like `a`.


**Aside:** By the way, if you are familiar with the *index-style* length
encoding e.g. as found in [DML][dml] or [Agda][agdavec], then its worth
noting that despite appearances, our `List` and `Point` definitions are
*not* indexed. We're just using the indices to define abbreviations for the
refinement predicates, and we have deliberately chosen the predicates to
facilitate SMT based checking and inference.

Basic Operations on Points and Clusters
=======================================

Ok, with the types firmly in hand, let us go forth and develop the KMeans
clustering implementation. We will use a variety of small helper functions
(of the kind found in `Data.List`.) Lets get started by looking at them
through our newly *refined* eyes.

Grouping
--------

The first such function is [groupBy][URL-groupBy]. We can
refine its type so that instead of just producing a `[[a]]`
we know that it produces a `Clustering a` which is a list
of *non-empty* lists.


<pre><span class=hs-linenum>124: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>groupBy</span>       <span class='hs-keyglyph'>::</span><span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Clustering</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>125: </span><a class=annot href="#"><span class=annottext>(a -&gt; a -&gt; (GHC.Types.Bool))
-&gt; [a] -&gt; {VV : [{VV : [a] | (len([VV]) &gt; 0)}] | (len([VV]) &gt;= 0)}</span><span class='hs-definition'>groupBy</span></a> <span class='hs-keyword'>_</span>  <span class='hs-conid'>[]</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [{VV : a | false}] | false}] | (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>126: </span><span class='hs-definition'>groupBy</span> <span class='hs-varid'>eq</span> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><a class=annot href="#"><span class=annottext>y:a -&gt; ys:[a] -&gt; {VV : [a] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),
            (VV = ys),
            (len([VV]) = len([ys])),
            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>y:{VV : [a] | (len([VV]) &gt; 0)}
-&gt; ys:[{VV : [a] | (len([VV]) &gt; 0)}]
-&gt; {VV : [{VV : [a] | (len([VV]) &gt; 0)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>(a -&gt; a -&gt; (GHC.Types.Bool))
-&gt; [a] -&gt; {VV : [{VV : [a] | (len([VV]) &gt; 0)}] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>groupBy</span></a> <a class=annot href="#"><span class=annottext>a -&gt; a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>eq</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = zs),
            (VV = zs),
            (len([VV]) = len([zs])),
            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>zs</span></a>
<span class=hs-linenum>127: </span>  <span class='hs-keyword'>where</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = ys),(len([VV]) = len([ys])),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a><span class='hs-layout'>,</span><a class=annot href="#"><span class=annottext>{VV : [a] | (VV = zs),(len([VV]) = len([zs])),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>zs</span></a><span class='hs-layout'>)</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>(a -&gt; (GHC.Types.Bool)) -&gt; [a] -&gt; ([a] , [a])</span><span class='hs-varid'>span</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>a -&gt; a -&gt; (GHC.Types.Bool)</span><span class='hs-varid'>eq</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

Intuitively, its pretty easy to see how LiquidHaskell verifies the refined
specification:

- Each element of the output list is of the form `x:ys`
- For any list `ys` the length is non-negative, i.e. `(len ys) >= 0`
- The `len` of `x:ys` is `1 + (len ys)`, that is, strictly positive.

Partitioning
------------

Next, lets look the function


<pre><span class=hs-linenum>143: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>partition</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>size</span><span class='hs-conop'>:</span><span class='hs-conid'>PosInt</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>Clustering</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>144: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>PosInt</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&gt;</span> <span class='hs-num'>0</span> <span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

which is given a *strictly positive* integer argument,
a list of `a` values, and returns a `Clustering a`,
that is, a list of non-empty lists. (Each inner list has a length
that is less than `size`, but we shall elide this for simplicity.)

The function is implemented in a straightforward manner, using the
library functions `take` and `drop`


<pre><span class=hs-linenum>156: </span><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt; 0)}
-&gt; [a] -&gt; {VV : [{VV : [a] | (len([VV]) &gt; 0)}] | (len([VV]) &gt;= 0)}</span><span class='hs-definition'>partition</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt; 0)}</span><span class='hs-varid'>size</span></a> <span class='hs-conid'>[]</span>       <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [{VV : a | false}] | false}] | (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>157: </span><span class='hs-definition'>partition</span> <span class='hs-varid'>size</span> <span class='hs-varid'>ys</span><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-keyword'>_</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = zs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>zs</span></a> <a class=annot href="#"><span class=annottext>y:{VV : [a] | (len([VV]) &gt; 0)}
-&gt; ys:[{VV : [a] | (len([VV]) &gt; 0)}]
-&gt; {VV : [{VV : [a] | (len([VV]) &gt; 0)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt; 0)}
-&gt; [a] -&gt; {VV : [{VV : [a] | (len([VV]) &gt; 0)}] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>partition</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = size),(VV &gt; 0)}</span><span class='hs-varid'>size</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = zs'),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>zs'</span></a>
<span class=hs-linenum>158: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>159: </span>    <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>zs</span></a>                  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>n:{VV : (GHC.Types.Int) | (VV &gt;= 0)}
-&gt; xs:[a]
-&gt; {VV : [a] | (len([VV]) = ((len([xs]) &lt; n) ? len([xs]) : n))}</span><span class='hs-varid'>take</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = size),(VV &gt; 0)}</span><span class='hs-varid'>size</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
<span class=hs-linenum>160: </span>    <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>zs'</span></a>                 <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>n:{VV : (GHC.Types.Int) | (VV &gt;= 0)}
-&gt; xs:[a]
-&gt; {VV : [a] | (len([VV]) = ((len([xs]) &lt; n) ? 0 : (len([xs]) - n)))}</span><span class='hs-varid'>drop</span></a> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = size),(VV &gt; 0)}</span><span class='hs-varid'>size</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>ys</span></a>
</pre>

To verify that a valid `Clustering` is produced, LiquidHaskell needs only
verify that the list `zs` above is non-empty, by suitably connecting the
properties of the inputs `size` and `ys` with the output.

 We have [verified elsewhere][URL-take] that
<pre><span class=hs-linenum>168: </span><span class='hs-definition'>take</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>n</span><span class='hs-conop'>:</span><span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&gt;=</span> <span class='hs-num'>0</span> <span class='hs-layout'>}</span>
<span class=hs-linenum>169: </span>     <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>170: </span>     <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-keyword'>if</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span> <span class='hs-keyword'>then</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyword'>else</span> <span class='hs-varid'>n</span><span class='hs-layout'>)</span> <span class='hs-layout'>}</span>
</pre>

In other words, the output list's length is the *smaller of* the input
list's length and `n`.  Thus, since both `size` and the `(len ys)` are
greater than `1`, LiquidHaskell deduces that the list returned by `take
size ys` has a length greater than `1`, i.e., is non-empty.

Zipping
-------

To compute the *Euclidean distance* between two points, we will use
the `zipWith` function. We must make sure that it is invoked on points
with the same number of dimensions, so we write


<pre><span class=hs-linenum>186: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>zipWith</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>c</span><span class='hs-layout'>)</span>
<span class=hs-linenum>187: </span>            <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>List</span> <span class='hs-varid'>b</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>(</span><span class='hs-conid'>List</span> <span class='hs-varid'>c</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>188: </span><a class=annot href="#"><span class=annottext>(a -&gt; b -&gt; c)
-&gt; x4:[a]
-&gt; x2:{VV : [b] | (len([VV]) = len([x4])),(len([VV]) &gt;= 0)}
-&gt; {VV : [c] | (len([VV]) = len([x4])),
               (len([VV]) = len([x2])),
               (len([VV]) &gt;= 0)}</span><span class='hs-definition'>zipWith</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; c</span><span class='hs-varid'>f</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>a</span><span class='hs-conop'>:</span><span class='hs-keyword'>as</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>b</span><span class='hs-conop'>:</span><span class='hs-varid'>bs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; c</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = a)}</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = b)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>y:a -&gt; ys:[a] -&gt; {VV : [a] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>(a -&gt; b -&gt; c)
-&gt; x4:[a]
-&gt; x2:{VV : [b] | (len([VV]) = len([x4])),(len([VV]) &gt;= 0)}
-&gt; {VV : [c] | (len([VV]) = len([x4])),
               (len([VV]) = len([x2])),
               (len([VV]) &gt;= 0)}</span><span class='hs-varid'>zipWith</span></a> <a class=annot href="#"><span class=annottext>a -&gt; b -&gt; c</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = as),(len([VV]) &gt;= 0)}</span><span class='hs-keyword'>as</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = bs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>bs</span></a>
<span class=hs-linenum>189: </span><span class='hs-definition'>zipWith</span> <span class='hs-keyword'>_</span> <span class='hs-conid'>[]</span> <span class='hs-conid'>[]</span>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | false}] | (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
</pre>

The type stipulates that the second input list and the output have
the same length as the first input. Furthermore, it rules out the
case where one list is empty and the other is not, as in that case
the former's length is zero while the latter's is not.

Transposing
-----------

The last basic operation that we will require is a means to
*transpose* a `Matrix`, which itself is just a list of lists:


<pre><span class=hs-linenum>204: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>Matrix</span> <span class='hs-varid'>a</span> <span class='hs-conid'>Rows</span> <span class='hs-conid'>Cols</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-conid'>List</span> <span class='hs-layout'>(</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-conid'>Cols</span><span class='hs-layout'>)</span> <span class='hs-conid'>Rows</span><span class='hs-layout'>)</span> <span class='hs-keyword'>@-}</span>
</pre>

The `transpose` operation flips the rows and columns. I confess that I
can never really understand matrices without concrete examples,
and even then, barely.

 So, lets say we have a *matrix*
<pre><span class=hs-linenum>212: </span><span class='hs-definition'>m1</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Matrix</span> <span class='hs-conid'>Int</span> <span class='hs-num'>4</span> <span class='hs-num'>2</span>
<span class=hs-linenum>213: </span><span class='hs-definition'>m1</span>  <span class='hs-keyglyph'>=</span>  <span class='hs-keyglyph'>[</span> <span class='hs-keyglyph'>[</span><span class='hs-num'>1</span><span class='hs-layout'>,</span> <span class='hs-num'>2</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>214: </span>       <span class='hs-layout'>,</span> <span class='hs-keyglyph'>[</span><span class='hs-num'>3</span><span class='hs-layout'>,</span> <span class='hs-num'>4</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>215: </span>       <span class='hs-layout'>,</span> <span class='hs-keyglyph'>[</span><span class='hs-num'>5</span><span class='hs-layout'>,</span> <span class='hs-num'>6</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>216: </span>       <span class='hs-layout'>,</span> <span class='hs-keyglyph'>[</span><span class='hs-num'>7</span><span class='hs-layout'>,</span> <span class='hs-num'>8</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>]</span>
</pre>

 then the matrix `m2 = transpose 2 3 m1` should be
<pre><span class=hs-linenum>220: </span><span class='hs-definition'>m2</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Matrix</span> <span class='hs-conid'>Int</span> <span class='hs-num'>2</span> <span class='hs-num'>4</span>
<span class=hs-linenum>221: </span><span class='hs-definition'>m2</span>  <span class='hs-keyglyph'>=</span>  <span class='hs-keyglyph'>[</span> <span class='hs-keyglyph'>[</span><span class='hs-num'>1</span><span class='hs-layout'>,</span> <span class='hs-num'>3</span><span class='hs-layout'>,</span> <span class='hs-num'>5</span><span class='hs-layout'>,</span> <span class='hs-num'>7</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>222: </span>       <span class='hs-layout'>,</span> <span class='hs-keyglyph'>[</span><span class='hs-num'>2</span><span class='hs-layout'>,</span> <span class='hs-num'>4</span><span class='hs-layout'>,</span> <span class='hs-num'>6</span><span class='hs-layout'>,</span> <span class='hs-num'>8</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>]</span>
</pre>

We will use a `Matrix a m n` to represent a *single cluster* of `m` points
each of which has `n` dimensions. We will transpose the matrix to make it
easy to *sum* and *average* the points along *each* dimension, in order to
compute the *center* of the cluster.

As you can work out from the above, the code for `transpose` is quite
straightforward: each *output row* is simply the list of `head`s of
the *input rows*:


<pre><span class=hs-linenum>235: </span><span class='hs-definition'>transpose</span>       <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>236: </span>
<span class=hs-linenum>237: </span><a class=annot href="#"><span class=annottext>c:(GHC.Types.Int)
-&gt; r:{VV : (GHC.Types.Int) | (VV &gt; 0)}
-&gt; {v : [{VV : [a] | (len([VV]) = c)}] | (len([v]) = r)}
-&gt; {v : [{VV : [a] | (len([VV]) = r)}] | (len([v]) = c)}</span><span class='hs-definition'>transpose</span></a> <span class='hs-num'>0</span> <span class='hs-keyword'>_</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [{VV : a | false}] | false}] | (len([VV]) = 0)}</span><span class='hs-conid'>[]</span></a>
<span class=hs-linenum>238: </span>
<span class=hs-linenum>239: </span><span class='hs-definition'>transpose</span> <span class='hs-varid'>c</span> <span class='hs-varid'>r</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-varid'>col00</span> <span class='hs-conop'>:</span> <span class='hs-varid'>col01s</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>row1s</span><span class='hs-layout'>)</span>
<span class=hs-linenum>240: </span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = row0'),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>row0'</span></a> <a class=annot href="#"><span class=annottext>y:{VV : [a] | (len([VV]) = len([row0'])),
              (len([VV]) = len([rest])),
              (len([VV]) &gt; 0)}
-&gt; ys:[{VV : [a] | (len([VV]) = len([row0'])),
                   (len([VV]) = len([rest])),
                   (len([VV]) &gt; 0)}]
-&gt; {VV : [{VV : [a] | (len([VV]) = len([row0'])),
                      (len([VV]) = len([rest])),
                      (len([VV]) &gt; 0)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{v : [[a]] | (v = row1s'),(len([v]) &gt;= 0)}</span><span class='hs-varid'>row1s'</span></a>
<span class=hs-linenum>241: </span>    <span class='hs-keyword'>where</span>
<span class=hs-linenum>242: </span>      <a class=annot href="#"><span class=annottext>[a]</span><span class='hs-varid'>row0'</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (VV = col00)}</span><span class='hs-varid'>col00</span></a>  <a class=annot href="#"><span class=annottext>y:a -&gt; ys:[a] -&gt; {VV : [a] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (len([VV]) = len([row1s])),(len([VV]) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = col0)}</span><span class='hs-varid'>col0</span></a>  <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>col0</span> <span class='hs-conop'>:</span> <span class='hs-keyword'>_</span><span class='hs-layout'>)</span>  <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>{VV : [[a]] | (VV = row1s),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>row1s</span></a> <span class='hs-keyglyph'>]</span>
<span class=hs-linenum>243: </span>      <a class=annot href="#"><span class=annottext>[{VV : [a] | (len([VV]) = len([col01s])),(len([VV]) &gt;= 0)}]</span><span class='hs-varid'>rest</span></a>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = col01s),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>col01s</span></a> <a class=annot href="#"><span class=annottext>y:{VV : [a] | (len([VV]) = len([col01s])),(len([VV]) &gt;= 0)}
-&gt; ys:[{VV : [a] | (len([VV]) = len([col01s])),(len([VV]) &gt;= 0)}]
-&gt; {VV : [{VV : [a] | (len([VV]) = len([col01s])),
                      (len([VV]) &gt;= 0)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : [a] | (len([VV]) = len([col01s])),
                   (len([VV]) &gt;= 0)}] | (len([VV]) = len([row1s])),(len([VV]) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a> <a class=annot href="#"><span class=annottext>{VV : [a] | (VV = col1s),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>col1s</span></a> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-keyword'>_</span> <span class='hs-conop'>:</span> <span class='hs-varid'>col1s</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>{VV : [[a]] | (VV = row1s),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>row1s</span></a> <span class='hs-keyglyph'>]</span>
<span class=hs-linenum>244: </span>      <a class=annot href="#"><span class=annottext>[[a]]</span><span class='hs-varid'>row1s'</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>c:(GHC.Types.Int)
-&gt; r:{VV : (GHC.Types.Int) | (VV &gt; 0)}
-&gt; {v : [{VV : [a] | (len([VV]) = c)}] | (len([v]) = r)}
-&gt; {v : [{VV : [a] | (len([VV]) = r)}] | (len([v]) = c)}</span><span class='hs-varid'>transpose</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(GHC.Types.Int)</span><span class='hs-varid'>c</span></a><a class=annot href="#"><span class=annottext>x:(GHC.Types.Int)
-&gt; y:(GHC.Types.Int) -&gt; {VV : (GHC.Types.Int) | (VV = (x - y))}</span><span class='hs-comment'>-</span></a><a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : (GHC.Types.Int) | (VV &gt; 0)}</span><span class='hs-varid'>r</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : [a] | (len([VV]) = len([col01s])),
                   (len([VV]) &gt;= 0)}] | (VV = rest),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>rest</span></a>
</pre>

LiquidHaskell verifies that


<pre><span class=hs-linenum>250: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>transpose</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>c</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>r</span><span class='hs-conop'>:</span><span class='hs-conid'>PosInt</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Matrix</span> <span class='hs-varid'>a</span> <span class='hs-varid'>r</span> <span class='hs-varid'>c</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Matrix</span> <span class='hs-varid'>a</span> <span class='hs-varid'>c</span> <span class='hs-varid'>r</span> <span class='hs-keyword'>@-}</span>
</pre>

Try to work it out for yourself on pencil and paper.

If you like you can get a hint by seeing how LiquidHaskell figures it out.
Lets work *backwards*.

 LiquidHaskell verifies the output type by inferring that
<pre><span class=hs-linenum>259: </span><span class='hs-definition'>row0'</span>        <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-varid'>r</span><span class='hs-layout'>)</span>
<span class=hs-linenum>260: </span><span class='hs-definition'>row1s'</span>       <span class='hs-keyglyph'>::</span> <span class='hs-conid'>List</span> <span class='hs-layout'>(</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-varid'>r</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>c</span> <span class='hs-comment'>-</span> <span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-comment'>-- i.e. Matrix a (c - 1) r</span>
</pre>

 and so, by simply using the *measure-refined* type for `:`
<pre><span class=hs-linenum>264: </span><span class='hs-layout'>(</span><span class='hs-conop'>:</span><span class='hs-layout'>)</span>          <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span> <span class='hs-varid'>v</span> <span class='hs-conop'>:</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-layout'>}</span>
</pre>

 LiquidHaskell deduces that
<pre><span class=hs-linenum>268: </span><span class='hs-definition'>row0</span> <span class='hs-conop'>:</span> <span class='hs-varid'>rows'</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>List</span> <span class='hs-layout'>(</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-varid'>r</span><span class='hs-layout'>)</span> <span class='hs-varid'>c</span>
</pre>

 That is,
<pre><span class=hs-linenum>272: </span><span class='hs-definition'>row0</span> <span class='hs-conop'>:</span> <span class='hs-varid'>rows'</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Matrix</span> <span class='hs-varid'>a</span> <span class='hs-varid'>c</span> <span class='hs-varid'>r</span>
</pre>

Excellent! Now, lets work backwards. How does it infer the types of `row0'` and `row1s'`?

The first case is easy: `row0'` is just the list of *heads* of each row, hence a `List a r`.

 Now, lets look at `row1s'`. Notice that `row1s` is the matrix of all *except* the first row of the input Matrix, and so
<pre><span class=hs-linenum>280: </span><span class='hs-definition'>row1s</span>        <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Matrix</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-varid'>r</span><span class='hs-comment'>-</span><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varid'>c</span>
</pre>

 and so, as
<pre><span class=hs-linenum>284: </span><span class='hs-definition'>col01s</span>       <span class='hs-keyglyph'>::</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-varid'>c</span><span class='hs-comment'>-</span><span class='hs-num'>1</span><span class='hs-layout'>)</span>
<span class=hs-linenum>285: </span><span class='hs-definition'>col1s</span>        <span class='hs-keyglyph'>::</span> <span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-varid'>c</span><span class='hs-comment'>-</span><span class='hs-num'>1</span><span class='hs-layout'>)</span>
</pre>

 LiquidHaskell deduces that since `rest` is the concatenation of `r-1` tails from `row1s`
<pre><span class=hs-linenum>289: </span><span class='hs-definition'>rest</span>         <span class='hs-keyglyph'>=</span> <span class='hs-varid'>col01s</span> <span class='hs-conop'>:</span> <span class='hs-keyglyph'>[</span> <span class='hs-varid'>col1s</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-keyword'>_</span> <span class='hs-conop'>:</span> <span class='hs-varid'>col1s</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>&lt;-</span> <span class='hs-varid'>row1s</span> <span class='hs-keyglyph'>]</span>
</pre>

 the type of `rest` is
<pre><span class=hs-linenum>293: </span><span class='hs-definition'>rest</span>         <span class='hs-keyglyph'>::</span> <span class='hs-conid'>List</span> <span class='hs-layout'>(</span><span class='hs-conid'>List</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-varid'>c</span> <span class='hs-comment'>-</span> <span class='hs-num'>1</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span> <span class='hs-varid'>r</span>
</pre>

 which is just
<pre><span class=hs-linenum>297: </span><span class='hs-definition'>rest</span>         <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Matrix</span> <span class='hs-varid'>a</span> <span class='hs-varid'>r</span> <span class='hs-layout'>(</span><span class='hs-varid'>c</span><span class='hs-comment'>-</span><span class='hs-num'>1</span><span class='hs-layout'>)</span>
</pre>

Now, LiquidHaskell deduces `row1s' :: Matrix a (c-1) r` by inductively
plugging in the output type of the recursive call, thereby checking the
function's signature.


*Whew!* That was a fair bit of work, wasn't it!

Happily, we didn't have to do *any* of it. Instead, using the SMT solver,
LiquidHaskell ploughs through calculations like that and guarantees to us
that `transpose` indeed flips the dimensions of the inner and outer lists.

**Aside: Comprehensions vs. Map** Incidentally, the code above is essentially
that of `transpose` [from the Prelude][URL-transpose] with some extra
local variables for exposition. You could instead use a `map head` and `map tail`
and I encourage you to go ahead and [see for yourself.][demo]

Intermission
------------

Time for a break -- [go see a cat video!][maru] -- or skip it, stretch your
legs, and return post-haste for the [next installment][kmeansII], in which
we will use the types and functions described above, to develop the clustering
algorithm.

[safeList]:      /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/
[kmeansI]:       /blog/2013/02/16/kmeans-clustering-I.lhs/
[kmeansII]:      /blog/2013/02/17/kmeans-clustering-II.lhs/
[URL-take]:      https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/List.lhs#L334
[URL-groupBy]:   http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-List.html#v:groupBy
[URL-transpose]: http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#transpose
[maru]:          http://www.youtube.com/watch?v=8uDuls5TyNE
[demo]:          http://goto.ucsd.edu/~rjhala/liquid/haskell/demo/#?demo=KMeansHelper.hs
[URL-kmeans]:    http://hackage.haskell.org/package/kmeans
[dml]:           http://www.cs.bu.edu/~hwxi/DML/DML.html
[agdavec]:       http://code.haskell.org/Agda/examples/Vec.agda

