---
layout: post
title: "Parametric Invariants via Abstract Refinements"
date: 2013-01-10 16:12
comments: true
external-url:
categories: abstract refinements
author: Niki Vazou
published: false
---

Lets see how *abstract refinements* can be used to express *parametric invariants* 
over base types and *typeclasses*. 


<pre><span class=hs-linenum>16: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Toy</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>17: </span>
<span class=hs-linenum>18: </span><span class='hs-keyword'>import</span> <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>Prelude</span> <span class='hs-layout'>(</span><span class='hs-varid'>isEven</span><span class='hs-layout'>)</span>
</pre>

Parametric Invariants over Base Types
-------------------------------------

Suppose we have a monomorphic `max` function on `Int` values:

<pre><span class=hs-linenum>26: </span><span class='hs-definition'>maxInt</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> 
<span class=hs-linenum>27: </span><a class=annot href="#"><span class=annottext>forall &lt;p :: (Int) -&gt; Bool&gt;. (Int)&lt;p 0&gt; -&gt; (Int)&lt;p 0&gt; -&gt; (Int)&lt;p 0&gt;</span><span class='hs-definition'>maxInt</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (? papp1([p; VV]))}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (? papp1([p; VV]))}</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>if</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (? papp1([p; VV])),(VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:{VV : (Int) | (? papp1([p; VV]))}
-&gt; y:{VV : (Int) | (? papp1([p; VV]))}
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (? papp1([p; VV])),(VV = y)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyword'>then</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (? papp1([p; VV])),(VV = y)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyword'>else</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (? papp1([p; VV])),(VV = x)}</span><span class='hs-varid'>x</span></a> 
</pre>

`maxInt` could take many refinement types, for example
<pre><span class=hs-linenum>31: </span><span class='hs-definition'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&gt;</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&gt;</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&gt;</span> <span class='hs-num'>0</span><span class='hs-layout'>}</span>
</pre>

or
<pre><span class=hs-linenum>35: </span><span class='hs-definition'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&lt;</span> <span class='hs-num'>10</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&lt;</span> <span class='hs-num'>10</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>v</span> <span class='hs-varop'>&lt;</span> <span class='hs-num'>10</span><span class='hs-layout'>}</span>
</pre>

or even 
<pre><span class=hs-linenum>39: </span><span class='hs-definition'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>prime</span><span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>prime</span><span class='hs-layout'>(</span><span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>prime</span><span class='hs-layout'>(</span><span class='hs-varid'>v</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span>
</pre>

We can prove that if a property holds for both  `x` and `y`, then it also holds for `maxInt x y`.
So, we would like to _abstract_ over the refinements that both arguments and the result have.
We can acchieve this with with _abstract refinements_, which let us quantify or parameterize a type over its constituent refinements.  For example, we can type `maxInt` as

<pre><span class=hs-linenum>46: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maxInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span><span class='hs-keyword'>@-}</span>
</pre>

where `Int<p>` is an abbreviation for the refinement type `{v:Int | p(v)}`.
Intuitively, an abstract refinement `p` is encoded in the refinement logic 
as an _uninterpreted function symbol_, which satisfies the
_congruence axiom_

~~~
forall X, Y. X = Y => P(X) = P(Y)
~~~

Thus, it is trivial to verify, with an SMT solver, that `maxInt` 
enjoys the above type: the input types ensure that both `p(x)` and `p(y)` 
hold and hence the returned value in either branch satisfies 
the refinement  `{v:Int | p(v)}`, thereby ensuring the output 
type. 

By the same reasoning, we can define the `maximumInt` operator on lists:

<pre><span class=hs-linenum>66: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maximumInt</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span><span class='hs-keyword'>@-}</span>
<span class=hs-linenum>67: </span><span class='hs-definition'>maximumInt</span> <span class='hs-keyglyph'>::</span>  <span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> 
<span class=hs-linenum>68: </span><a class=annot href="#"><span class=annottext>forall &lt;p :: (Int) -&gt; Bool&gt;. [(Int)&lt;p 0&gt;] -&gt; (Int)&lt;p 0&gt;</span><span class='hs-definition'>maximumInt</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>({VV : (Int) | (? papp1([p; VV]))}
 -&gt; {VV : (Int) | (? papp1([p; VV]))}
 -&gt; {VV : (Int) | (? papp1([p; VV]))})
-&gt; {VV : (Int) | (? papp1([p; VV]))}
-&gt; [{VV : (Int) | (? papp1([p; VV]))}]
-&gt; {VV : (Int) | (? papp1([p; VV]))}</span><span class='hs-varid'>foldr</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: (Int) -&gt; Bool&gt;. (Int)&lt;p 0&gt; -&gt; (Int)&lt;p 0&gt; -&gt; (Int)&lt;p 0&gt;</span><span class='hs-varid'>maxInt</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (? papp1([p; VV])),(VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : (Int) | (? papp1([p; VV]))}] | (VV = xs),
                                            (len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>

Now, we can use the function `isEven` from Language.Haskell.Liquid.Prelude library:
<pre><span class=hs-linenum>72: </span><span class='hs-comment'>{- assume isEven :: x:Int -&gt; {v:Bool | (Prop(v) &lt;=&gt; ((x mod 2) = 0))} -}</span>
<span class=hs-linenum>73: </span><span class='hs-definition'>isEven</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>74: </span><span class='hs-definition'>isEven</span> <span class='hs-varid'>x</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>x</span> <span class='hs-varop'>`mod`</span> <span class='hs-num'>2</span> <span class='hs-varop'>==</span> <span class='hs-num'>0</span>
</pre>

And write a function `maxEvens`.

<pre><span class=hs-linenum>79: </span><a class=annot href="#"><span class=annottext>[(Int)] -&gt; {VV : (Int) | ((VV mod 2) = 0)}</span><span class='hs-definition'>maxEvens1</span></a> <a class=annot href="#"><span class=annottext>[(Int)]</span><span class='hs-varid'>xs</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>forall &lt;p :: (Int) -&gt; Bool&gt;. [(Int)&lt;p 0&gt;] -&gt; (Int)&lt;p 0&gt;</span><span class='hs-varid'>maximumInt</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : (Int) | ((VV mod 2) = 0)}] | (VV = xs''),
                                          (len([VV]) = (1 + len([xs']))),
                                          (len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs''</span></a>
<span class=hs-linenum>80: </span>  <span class='hs-keyword'>where</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : (Int) | ((VV mod 2) = 0)}] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs'</span></a>  <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = ds_dtc)}</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>x</span> <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>{VV : [(Int)] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>x:(Int) -&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; ((x mod 2) = 0))}</span><span class='hs-varid'>isEven</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = ds_dtc)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>81: </span>        <a class=annot href="#"><span class=annottext>{VV : [{VV : (Int) | ((VV mod 2) = 0)}] | (len([VV]) = (1 + len([xs'])))}</span><span class='hs-varid'>xs''</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: (Int) -&gt; (Int) -&gt; Bool&gt;.
y:{VV : (Int) | ((VV mod 2) = 0)}
-&gt; ys:[{VV : (Int)&lt;p (fld, EVar y) 1&gt; | ((VV mod 2) = 0)}]
-&gt; {VV : [{VV : (Int) | ((VV mod 2) = 0)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : (Int) | ((VV mod 2) = 0)}] | (VV = xs'),
                                          (len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs'</span></a>
</pre>

Since `(0:xs')` is a list if values with type 
`{v:Int | (x mod 2) = 0}`, 
we can instantiate
the _refinement_ parameter of `maximumInt` with the concrete 
refinement 
`{\v -> v mod 2) = 0}`,
after which type of `maxEvens1` can be proved to be:


<pre><span class=hs-linenum>93: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maxEvens1</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v mod 2 = 0 }</span> <span class='hs-keyword'>@-}</span>
</pre>

Parametric Invariants over Class-Predicated Type Variables
----------------------------------------------------------

The example above regularly arises in practice, due to type classes. 
In Haskell, the functions above are typed
<pre><span class=hs-linenum>101: </span><span class='hs-layout'>(</span><span class='hs-varop'>&lt;=</span><span class='hs-layout'>)</span>    <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>102: </span><span class='hs-definition'>max</span>     <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>103: </span><span class='hs-definition'>maximum</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
</pre>

We might be tempted to simply ignore the type class constraint, 
and just treat `maximum` as `[a] -> a` but, of course, 
this would be quite unsound, as typeclass predicates trivially preclude
universal quantification over refinement types. 
Consider the function `sum :: (Num a) => [a] -> a` which adds the elements 
of a list.

The `Num` class constraint implies that numeric operations occur 
in the function, so
if we pass `sum` a list of odd numbers, 
we are _not_ guaranteed to get back an odd number. 

Thus, how do we soundly verify the desired type of `maxEvens`
without instantiating class predicated type parameters with 
arbitrary refinement types? First, via the same analysis as 
the monomorphic `Int` case, we establish that


<pre><span class=hs-linenum>124: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maxPoly</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>y</span><span class='hs-conop'>:</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>125: </span><span class='hs-definition'>maxPoly</span>     <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> 
<span class=hs-linenum>126: </span><a class=annot href="#"><span class=annottext>forall a &lt;p :: a -&gt; Bool&gt;. (Ord a) -&gt; a&lt;p 0&gt; -&gt; a&lt;p 0&gt; -&gt; a&lt;p 0&gt;</span><span class='hs-definition'>maxPoly</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (? papp1([p; VV]))}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (? papp1([p; VV]))}</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <span class='hs-keyword'>if</span> <a class=annot href="#"><span class=annottext>{VV : a | (? papp1([p; VV])),(VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x:{VV : a | (? papp1([p; VV]))}
-&gt; y:{VV : a | (? papp1([p; VV]))}
-&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; (x &lt;= y))}</span><span class='hs-varop'>&lt;=</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (? papp1([p; VV])),(VV = y)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyword'>then</span> <a class=annot href="#"><span class=annottext>{VV : a | (? papp1([p; VV])),(VV = y)}</span><span class='hs-varid'>y</span></a> <span class='hs-keyword'>else</span> <a class=annot href="#"><span class=annottext>{VV : a | (? papp1([p; VV])),(VV = x)}</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>127: </span>
<span class=hs-linenum>128: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maximumPoly</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyword'>forall</span> <span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Prop</span><span class='hs-varop'>&gt;.</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span><span class='hs-varop'>&lt;</span><span class='hs-varid'>p</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>129: </span><span class='hs-definition'>maximumPoly</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>a</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>130: </span><a class=annot href="#"><span class=annottext>forall a &lt;p :: a -&gt; Bool&gt;. (Ord a) -&gt; [a&lt;p 0&gt;] -&gt; a&lt;p 0&gt;</span><span class='hs-definition'>maximumPoly</span></a> <span class='hs-layout'>(</span><span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-varid'>xs</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>({VV : a | (? papp1([p; VV]))}
 -&gt; {VV : a | (? papp1([p; VV]))} -&gt; {VV : a | (? papp1([p; VV]))})
-&gt; {VV : a | (? papp1([p; VV]))}
-&gt; [{VV : a | (? papp1([p; VV]))}]
-&gt; {VV : a | (? papp1([p; VV]))}</span><span class='hs-varid'>foldr</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (? papp1([p; VV]))}
-&gt; {VV : a | (? papp1([p; VV]))} -&gt; {VV : a | (? papp1([p; VV]))}</span><span class='hs-varid'>maxPoly</span></a> <a class=annot href="#"><span class=annottext>{VV : a | (? papp1([p; VV])),(VV = x)}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : a | (? papp1([p; VV]))}] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a>
</pre>


We can define `maxEvens2` that uses the above functions:


<pre><span class=hs-linenum>137: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>maxEvens2</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>xs</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>Int</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v:</span><span class='hs-conid'>Int</span> <span class='hs-keyword'>| v mod 2 = 0 }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>138: </span><a class=annot href="#"><span class=annottext>[(Int)] -&gt; {VV : (Int) | ((VV mod 2) = 0)}</span><span class='hs-definition'>maxEvens2</span></a> <a class=annot href="#"><span class=annottext>[(Int)]</span><span class='hs-varid'>xs</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[{VV : (Int) | ((VV mod 2) = 0)}]
-&gt; {VV : (Int) | ((VV mod 2) = 0)}</span><span class='hs-varid'>maximumPoly</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : (Int) | ((VV mod 2) = 0)}] | (VV = xs''),
                                          (len([VV]) = (1 + len([xs']))),
                                          (len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs''</span></a>
<span class=hs-linenum>139: </span>  <span class='hs-keyword'>where</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : (Int) | ((VV mod 2) = 0)}] | (len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs'</span></a>  <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = ds_dt4)}</span><span class='hs-varid'>x</span></a> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>x</span> <span class='hs-keyglyph'>&lt;-</span> <a class=annot href="#"><span class=annottext>{VV : [(Int)] | (VV = xs),(len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>x:(Int) -&gt; {VV : (Bool) | ((? Prop([VV])) &lt;=&gt; ((x mod 2) = 0))}</span><span class='hs-varid'>isEven</span></a> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = ds_dt4)}</span><span class='hs-varid'>x</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>140: </span>        <a class=annot href="#"><span class=annottext>{VV : [{VV : (Int) | ((VV mod 2) = 0)}] | (len([VV]) = (1 + len([xs'])))}</span><span class='hs-varid'>xs''</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{VV : (Int) | (VV = (0  :  int))}</span><span class='hs-num'>0</span></a> <a class=annot href="#"><span class=annottext>forall &lt;p :: (Int) -&gt; (Int) -&gt; Bool&gt;.
y:{VV : (Int) | ((VV mod 2) = 0)}
-&gt; ys:[{VV : (Int)&lt;p (fld, EVar y) 1&gt; | ((VV mod 2) = 0)}]
-&gt; {VV : [{VV : (Int) | ((VV mod 2) = 0)}] | (len([VV]) = (1 + len([ys])))}</span><span class='hs-conop'>:</span></a><a class=annot href="#"><span class=annottext>{VV : [{VV : (Int) | ((VV mod 2) = 0)}] | (VV = xs'),
                                          (len([VV]) &gt;= 0)}</span><span class='hs-varid'>xs'</span></a>
</pre>


Finally, at the call-site for `maximumPoly` in `maxEvens2` we
instantiate the type variable `a` with `Int`, and 
the abstract refinement `p` with `{\v -> v % 2 = 0}`
after which, the verification proceeds as described
earlier (for the `Int` case).
Thus, abstract refinements allow us to quantify over 
invariants without relying on parametric polymorphism, 
even in the presence of type classes.
