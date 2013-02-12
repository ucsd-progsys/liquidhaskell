
---
layout: post
title: "Encoding Induction with Abstract Refinements"
date: 2013-02-20 16:12
comments: true
external-url:
categories: abstract-refinements 
author: Niki Vazou
published: false
---

In this example, we explain how abstract refinements allow us to formalize
some kinds of structural induction within the type system. 


<pre><span class=hs-linenum>17: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Inductive</span> <span class='hs-keyword'>where</span>
</pre>

Measures
--------
First, lets define an inductive data type `Vec`


<pre><span class=hs-linenum>25: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Nil</span> <span class='hs-keyglyph'>|</span> <span class='hs-conid'>Cons</span> <span class='hs-varid'>a</span> <span class='hs-layout'>(</span><span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span>
</pre>

And let us formalize a notion of _length_ for lists within the refinement logic. 

To do so, we define a special `llen` measure by structural induction


<pre><span class=hs-linenum>33: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>measure</span> <span class='hs-varid'>llen</span>     <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span><span class='hs-varop'>.</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> 
<span class=hs-linenum>34: </span>    <span class='hs-varid'>llen</span> <span class='hs-layout'>(</span><span class='hs-conid'>Nil</span><span class='hs-layout'>)</span>       <span class='hs-keyglyph'>=</span> <span class='hs-num'>0</span> 
<span class=hs-linenum>35: </span>    <span class='hs-varid'>llen</span> <span class='hs-layout'>(</span><span class='hs-conid'>Cons</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-num'>1</span> <span class='hs-varop'>+</span> <span class='hs-varid'>llen</span><span class='hs-layout'>(</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span>
<span class=hs-linenum>36: </span>  <span class='hs-keyword'>@-}</span>
</pre>


Note that the symbol `llen` is encoded as an _uninterpreted_ function in the refinement logic, and is, except for the congruence axiom, opaque to the SMT solver. The measures are guaranteed, by construction, to terminate, and so we can soundly use them as uninterpreted functions in the refinement logic. Notice also, that we can define _multiple_ measures for a type; in this case we simply conjoin the refinements from each measure when refining each data constructor.

As a warmup, lets check that a _real_ length function indeed computes the length of the list:


<pre><span class=hs-linenum>45: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>sizeOf</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = llen(xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>46: </span><span class='hs-definition'>sizeOf</span>             <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>47: </span><a class=annot href="#"><span class=annottext>forall a. xs:(Vec a) -&gt; {VV : (Int) | (VV = llen([xs]))}</span><span class='hs-definition'>sizeOf</span></a> <span class='hs-conid'>Nil</span>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x:(Int#) -&gt; {VV : (Int) | (VV = (x  :  int))}</span><span class='hs-num'>0</span></a>
<span class=hs-linenum>48: </span><span class='hs-definition'>sizeOf</span> <span class='hs-layout'>(</span><span class='hs-conid'>Cons</span> <span class='hs-keyword'>_</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a> <a class=annot href="#"><span class=annottext>x:(Int) -&gt; y:(Int) -&gt; {VV : (Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>xs:(Vec a) -&gt; {VV : (Int) | (VV = llen([xs]))}</span><span class='hs-varid'>sizeOf</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vec a) | (VV = xs)}</span><span class='hs-varid'>xs</span></a>
</pre>



With these strengthened constructor types, we can verify, for example, that `myappend` produces a list whose length is the sum of the input lists'
lengths:


<pre><span class=hs-linenum>57: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>myappend</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>l</span><span class='hs-conop'>:</span> <span class='hs-layout'>(</span><span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>m</span><span class='hs-conop'>:</span> <span class='hs-layout'>(</span><span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>| llen(v)=llen(l)+llen(m)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>58: </span><a class=annot href="#"><span class=annottext>x4:(Vec a)
-&gt; x3:(Vec a)
-&gt; {VV : (Vec a) | (llen([VV]) = (llen([x4]) + llen([x3]))),
                   (llen([VV]) = (llen([x3]) + llen([x4])))}</span><span class='hs-definition'>myappend</span></a> <span class='hs-conid'>Nil</span>         <a class=annot href="#"><span class=annottext>(Vec a)</span><span class='hs-varid'>zs</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Vec a) | (VV = zs)}</span><span class='hs-varid'>zs</span></a>
<span class=hs-linenum>59: </span><span class='hs-definition'>myappend</span> <span class='hs-layout'>(</span><span class='hs-conid'>Cons</span> <span class='hs-varid'>y</span> <span class='hs-varid'>ys</span><span class='hs-layout'>)</span> <span class='hs-varid'>zs</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>a -&gt; xs:(Vec a) -&gt; {VV : (Vec a) | (llen([VV]) = (1 + llen([xs])))}</span><span class='hs-conid'>Cons</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = y)}</span><span class='hs-varid'>y</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x4:(Vec a)
-&gt; x3:(Vec a)
-&gt; {VV : (Vec a) | (llen([VV]) = (llen([x4]) + llen([x3]))),
                   (llen([VV]) = (llen([x3]) + llen([x4])))}</span><span class='hs-varid'>myappend</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vec a) | (VV = ys)}</span><span class='hs-varid'>ys</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vec a) | (VV = zs)}</span><span class='hs-varid'>zs</span></a><span class='hs-layout'>)</span>
</pre>


However, consider an alternate definition of `myappend` that uses `foldr`
<pre><span class=hs-linenum>64: </span><span class='hs-definition'>myappend'</span> <span class='hs-varid'>ys</span> <span class='hs-varid'>zs</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>foldr</span> <span class='hs-layout'>(</span><span class='hs-conop'>:</span><span class='hs-layout'>)</span> <span class='hs-varid'>zs</span> <span class='hs-varid'>ys</span> 
</pre>

where `foldr :: (a -> b -> b) -> b -> [a] -> b`.
It is unclear how to give `foldr` a (first-order) refinement type that captures the rather complex fact that the fold-function is ''applied'' all over the list argument, or, that it is a catamorphism. Hence, hitherto, it has not been possible to verify the second definition of `append`.


Typing Folds
------------

Abstract refinements allow us to solve this problem with a very expressive type for _foldr_ whilst remaining firmly within the boundaries of SMT-based decidability. We write a slightly modified fold:


<pre><span class=hs-linenum>77: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>efoldr</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varid'>a</span> <span class='hs-varid'>b</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x0</span><span class='hs-conop'>:</span><span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x1</span><span class='hs-conop'>:</span><span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> 
<span class=hs-linenum>78: </span>                <span class='hs-varid'>op</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-conop'>:</span><span class='hs-varid'>b</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>xs</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> 
<span class=hs-linenum>79: </span>                  <span class='hs-varid'>exists</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>xxs</span> <span class='hs-conop'>:</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>| v = (Inductive.Cons x xs)}</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>.</span>
<span class=hs-linenum>80: </span>                     <span class='hs-varid'>b</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>xxs</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>81: </span>              <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>vs</span><span class='hs-conop'>:</span><span class='hs-layout'>(</span><span class='hs-varid'>exists</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>zz</span><span class='hs-conop'>:</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>| v = Inductive.Nil}</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>.</span> <span class='hs-varid'>b</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>zz</span><span class='hs-varop'>&gt;</span><span class='hs-layout'>)</span> 
<span class=hs-linenum>82: </span>              <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>83: </span>              <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-varid'>ys</span><span class='hs-varop'>&gt;</span>
<span class=hs-linenum>84: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>85: </span><span class='hs-definition'>efoldr</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>b</span>
<span class=hs-linenum>86: </span><a class=annot href="#"><span class=annottext>forall a b &lt;p :: (Vec a) -&gt; b -&gt; Bool&gt;.
(xs:(Vec a)
 -&gt; x:a
 -&gt; b&lt;p (x0, EVar xs) 1&gt;
 -&gt; exists [xxs:{VV : (Vec a) | (VV = Cons([x; xs]))}].b&lt;p (x0,
                                                            EVar xxs) 1&gt;)
-&gt; exists [zz:{VV : (Vec a) | (VV = Nil([]))}].b&lt;p (x0, EVar zz) 1&gt;
-&gt; ys:(Vec a)
-&gt; b&lt;p (x0, EVar ys) 1&gt;</span><span class='hs-definition'>efoldr</span></a> <a class=annot href="#"><span class=annottext>x3:(Vec a)
-&gt; x1:a
-&gt; {VV : b | (? papp2([p; VV; x3]))}
-&gt; {VV : b | (? papp2([p; VV; Cons([x1; x3])]))}</span><span class='hs-varid'>op</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (? papp2([p; VV; Nil([])]))}</span><span class='hs-varid'>b</span></a> <span class='hs-conid'>Nil</span>         <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : a | (? papp2([p; VV; Nil([])])),(VV = b)}</span><span class='hs-varid'>b</span></a>
<span class=hs-linenum>87: </span><span class='hs-definition'>efoldr</span> <span class='hs-varid'>op</span> <span class='hs-varid'>b</span> <span class='hs-layout'>(</span><span class='hs-conid'>Cons</span> <span class='hs-varid'>x</span> <span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x3:(Vec a)
-&gt; x1:a
-&gt; {VV : b | (? papp2([p; VV; x3]))}
-&gt; {VV : b | (? papp2([p; VV; Cons([x1; x3])]))}</span><span class='hs-varid'>op</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vec a) | (VV = xs)}</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = x)}</span><span class='hs-varid'>x</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>forall &lt;p :: (Vec a) -&gt; b -&gt; Bool&gt;.
(xs:(Vec a)
 -&gt; x:a
 -&gt; b&lt;p (x0, EVar xs) 1&gt;
 -&gt; exists [xxs:{VV : (Vec a) | (VV = Cons([x; xs]))}].b&lt;p (x0,
                                                            EVar xxs) 1&gt;)
-&gt; exists [zz:{VV : (Vec a) | (VV = Nil([]))}].b&lt;p (x0, EVar zz) 1&gt;
-&gt; ys:(Vec a)
-&gt; b&lt;p (x0, EVar ys) 1&gt;</span><span class='hs-varid'>efoldr</span></a> <a class=annot href="#"><span class=annottext>x3:(Vec a)
-&gt; x1:a
-&gt; {VV : b | (? papp2([p; VV; x3]))}
-&gt; {VV : b | (? papp2([p; VV; Cons([x1; x3])]))}</span><span class='hs-varid'>op</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (? papp2([p; VV; Nil([])])),(VV = b)}</span><span class='hs-varid'>b</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vec a) | (VV = xs)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>)</span> 
</pre>

The trick is simply to quantify over the relationship `p` that `efoldr` establishes between the input list `xs` and the output `b` value. This is formalized by the type signature, which encodes an induction principle for lists: 
the base value `b` must (1) satisfy the relation with the empty list, and the function `op` must take (2) a value that satisfies the relationship with the tail `xs` (we have added the `xs` as an extra "ghost" parameter to `op`), (3) a head value `x`, and return (4) a new folded value that satisfies the relationship with `x:xs`.
If all the above are met, then the value returned by `efoldr` satisfies the relation with the input list `ys`.

This scheme is not novel in itself --- what is new is the encoding, via uninterpreted predicate symbols, in an SMT-decidable refinement type system.

Using Folds
-----------

Finally, we can use the expressive type for the above `foldr` to verify various inductive properties of client functions:


<pre><span class=hs-linenum>102: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>size</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = llen(xs)}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>103: </span><span class='hs-definition'>size</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>104: </span><a class=annot href="#"><span class=annottext>forall a. xs:(Vec a) -&gt; {VV : (Int) | (VV = llen([xs]))}</span><span class='hs-definition'>size</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (Vec a) -&gt; (Int) -&gt; Bool&gt;.
(xs:(Vec a)
 -&gt; x:a
 -&gt; {VV : (Int)&lt;p (x0, EVar xs) 1&gt; | (VV &gt;= 0)}
 -&gt; exists [xxs:{VV : (Vec a) | (VV = Cons([x;
                                            xs]))}].{VV : (Int)&lt;p (x0, EVar xxs) 1&gt; | (VV &gt;= 0)})
-&gt; exists [zz:{VV : (Vec a) | (VV = Nil([]))}].{VV : (Int)&lt;p (x0,
                                                              EVar zz) 1&gt; | (VV &gt;= 0)}
-&gt; ys:(Vec a)
-&gt; {VV : (Int)&lt;p (x0, EVar ys) 1&gt; | (VV &gt;= 0)}</span><span class='hs-varid'>efoldr</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>ds_di9:(Vec a)
-&gt; a
-&gt; n:{VV : (Int) | (VV = llen([ds_di9])),(VV &gt;= 0)}
-&gt; {VV : (Int) | (VV = (n + 1))}</span><span class='hs-keyglyph'>\</span></a><span class='hs-keyword'>_</span> <span class='hs-keyword'>_</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = llen([ds_di9])),(VV &gt;= 0)}</span><span class='hs-varid'>n</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>x:(Int) -&gt; {VV : (Int) | (VV = (x + 1))}</span><span class='hs-varid'>suc</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = n),(VV = llen([ds_di9])),(VV &gt;= 0)}</span><span class='hs-varid'>n</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a>
<span class=hs-linenum>105: </span>
<span class=hs-linenum>106: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>suc</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Int</span> <span class='hs-keyword'>| v = x + 1}</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>107: </span><span class='hs-definition'>suc</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>108: </span><a class=annot href="#"><span class=annottext>x:(Int) -&gt; {VV : (Int) | (VV = (x + 1))}</span><span class='hs-definition'>suc</span></a> <a class=annot href="#"><span class=annottext>(Int)</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:(Int) -&gt; y:(Int) -&gt; {VV : (Int) | (VV = (x + y))}</span><span class='hs-varop'>+</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (1  :  int))}</span><span class='hs-num'>1</span></a> 
<span class=hs-linenum>109: </span>
<span class=hs-linenum>110: </span><span class='hs-keyword'>{-@</span> 
<span class=hs-linenum>111: </span>   <span class='hs-varid'>myappend'</span>  <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>ys</span><span class='hs-conop'>:</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span> <span class='hs-conid'>Vec</span> <span class='hs-varid'>a</span> <span class='hs-keyword'>| llen(v) = llen(xs) + llen(ys)}</span> 
<span class=hs-linenum>112: </span>  <span class='hs-keyword'>@-}</span> 
<span class=hs-linenum>113: </span><a class=annot href="#"><span class=annottext>forall a.
xs:(Vec a)
-&gt; ys:(Vec a)
-&gt; {VV : (Vec a) | (llen([VV]) = (llen([xs]) + llen([ys])))}</span><span class='hs-definition'>myappend'</span></a> <a class=annot href="#"><span class=annottext>(Vec a)</span><span class='hs-varid'>xs</span></a> <a class=annot href="#"><span class=annottext>(Vec a)</span><span class='hs-varid'>ys</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (Vec a) -&gt; (Vec a) -&gt; Bool&gt;.
(xs:(Vec a)
 -&gt; x:a
 -&gt; (Vec a)&lt;p (x0, EVar xs) 1&gt;
 -&gt; exists [xxs:{VV : (Vec a) | (VV = Cons([x;
                                            xs]))}].(Vec a)&lt;p (x0, EVar xxs) 1&gt;)
-&gt; exists [zz:{VV : (Vec a) | (VV = Nil([]))}].(Vec a)&lt;p (x0,
                                                          EVar zz) 1&gt;
-&gt; ys:(Vec a)
-&gt; (Vec a)&lt;p (x0, EVar ys) 1&gt;</span><span class='hs-varid'>efoldr</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>ds_dib:(Vec a)
-&gt; a
-&gt; zs:{VV : (Vec a) | (llen([VV]) = (llen([ds_dib]) + llen([ys]))),
                      (llen([VV]) = (llen([ys]) + llen([ds_dib])))}
-&gt; {VV : (Vec a) | (llen([VV]) = (1 + llen([zs])))}</span><span class='hs-keyglyph'>\</span></a><span class='hs-keyword'>_</span> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>z</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vec a) | (llen([VV]) = (llen([ds_dib]) + llen([ys]))),
                (llen([VV]) = (llen([ys]) + llen([ds_dib])))}</span><span class='hs-varid'>zs</span></a> <span class='hs-keyglyph'>-&gt;</span> <a class=annot href="#"><span class=annottext>a -&gt; xs:(Vec a) -&gt; {VV : (Vec a) | (llen([VV]) = (1 + llen([xs])))}</span><span class='hs-conid'>Cons</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (VV = z)}</span><span class='hs-varid'>z</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vec a) | (VV = zs),
                (llen([VV]) = (llen([ds_dib]) + llen([ys]))),
                (llen([VV]) = (llen([ys]) + llen([ds_dib])))}</span><span class='hs-varid'>zs</span></a><span class='hs-layout'>)</span> <a class=annot href="#"><span class=annottext>{VV : (Vec a) | (VV = ys)}</span><span class='hs-varid'>ys</span></a> <a class=annot href="#"><span class=annottext>{VV : (Vec a) | (VV = xs)}</span><span class='hs-varid'>xs</span></a> 
</pre>


The verification proceeds by just (automatically) instantiating the refinement parameter `p` of `efoldr` with the concrete refinements, via Liquid typing:
<pre><span class=hs-linenum>118: </span>
<span class=hs-linenum>119: </span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>xs</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>llen</span><span class='hs-layout'>(</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>                   <span class='hs-comment'>-- for size</span>
<span class=hs-linenum>120: </span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>xs</span> <span class='hs-varid'>v</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>llen</span><span class='hs-layout'>(</span><span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>llen</span><span class='hs-layout'>(</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-varop'>+</span> <span class='hs-varid'>llen</span><span class='hs-layout'>(</span><span class='hs-varid'>zs</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>  <span class='hs-comment'>-- for myappend'</span>
</pre>

