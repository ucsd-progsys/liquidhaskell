---
layout: post
title: Splitting and Splicing Intervals (Part 2)
date: 2017-12-24
comments: true
author: Ranjit Jhala
published: true
tags:
   - reflection
   - abstract-refinements
demo: RangeSet.hs
---

[Previously][splicing-1], we saw how the principle of
_"making illegal states unrepresentable"_ allowed LH
to easily enforce a _key invariant_ in
[Joachim](https://twitter.com/nomeata?lang=en)
Breitner's library for representing sets of integers
as [sorted lists of intervals][nomeata-intervals].

However, [Hs-to-coq][hs-to-coq] let Breitner
specify and verify that his code properly
implemented a _set_ library. Today, lets
see how LH's new _"type-level computation"_
abilities let us reason about the sets
of values corresponding to intervals,
while using the SMT solver to greatly
simplify the overhead of proof.

(Click here to [demo][demo])

<!-- more -->

<div class="row">
<div class="col-lg-2"></div>
<div class="col-lg-8">
<img src="../../static/img/ribbon.png" alt="Ribbons">
</div>
<div class="col-lg-2"></div>
</div>

<div class="hidden">

<pre><span class=hs-linenum>42: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--short-names"</span>    <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>43: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--exact-data-con"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>44: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-adt"</span>         <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>45: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--higherorder"</span>    <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>46: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--diff"</span>           <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>47: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--ple"</span>            <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>48: </span>
<span class=hs-linenum>49: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>RangeSet</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>50: </span>
<span class=hs-linenum>51: </span><span class='hs-keyword'>import</span>           <span class='hs-conid'>Prelude</span> <span class='hs-varid'>hiding</span> <span class='hs-layout'>(</span><span class='hs-varid'>min</span><span class='hs-layout'>,</span> <span class='hs-varid'>max</span><span class='hs-layout'>)</span>
<span class=hs-linenum>52: </span><span class='hs-keyword'>import</span>           <span class='hs-conid'>Language</span><span class='hs-varop'>.</span><span class='hs-conid'>Haskell</span><span class='hs-varop'>.</span><span class='hs-conid'>Liquid</span><span class='hs-varop'>.</span><span class='hs-conid'>NewProofCombinators</span>
</pre>
</div>


Intervals
---------

Recall that the key idea is to represent sets of integers like

```haskell
{ 7, 1, 10, 3, 11, 2, 9, 12, 4}
```

as ordered lists of *intervals*

```haskell
[ (1, 5), (7, 8), (9, 13) ]
```

where each pair `(i, j)` represents the set `{i, i+1,..., j-1}`.

To verify that the implementation correctly implements a set
data type, we need a way to

1. _Specify_ the set of values being described,
2. _Establish_ some key properties of these sets.

Range-Sets: Semantics of Intervals
----------------------------------

We can describe the set of values corresponding
to (i.e. "the semantics of") an interval `i, j`
by importing the `Data.Set` library


<pre><span class=hs-linenum>88: </span><span class='hs-keyword'>import</span> <span class='hs-keyword'>qualified</span> <span class='hs-conid'>Data</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> <span class='hs-keyword'>as</span> <span class='hs-conid'>S</span>
</pre>

to write a function `rng i j` that defines the **range-set** `i..j`


<pre><span class=hs-linenum>94: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reflect</span> <span class='hs-varid'>rng</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>95: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>rng</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>S</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-varop'>/</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>j</span> <span class='hs-comment'>-</span> <span class='hs-varid'>i</span><span class='hs-keyglyph'>]</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>96: </span><a class=annot href="#"><span class=annottext>Int -&gt; Int -&gt; (Set Int)</span><span class='hs-definition'>rng</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>j</span></a>
<span class=hs-linenum>97: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; i &lt; j}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>j</span>     <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : (Set Int) | v == Set_cup x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>union</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : (Set Int) | v == Set_sng i}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>singleton</span> <span class='hs-varid'>i</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>Int -&gt; Int -&gt; (Set Int)</span><span class='hs-varid'>rng</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varid'>j</span><span class='hs-layout'>)</span>
<span class=hs-linenum>98: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>S</span><span class='hs-varop'>.</span><span class='hs-varid'>empty</span>
</pre>

The `reflect rng` [tells LH][tag-reflection] that
we are going to want to work with the Haskell
function `rng` at the refinement-type level.


Equational Reasoning
--------------------

To build up a little intuition about the above
definition and how LH reasons about Sets, lets
write some simple _unit proofs_. For example,
lets check that `2` is indeed in the range-set
`rng 1 3`, by writing a type signature


<pre><span class=hs-linenum>116: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>test1</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>()</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{ S.member 2 (rng 1 3) }</span> <span class='hs-keyword'>@-}</span>
</pre>

Any _implementation_ of the above type is a _proof_
that `2` is indeed in `rng 1 3`. Notice that we can
reuse the operators from `Data.Set` (here, `S.member`)
to talk about set operations in the refinement logic.
Lets write this proof in an [equational style][bird-algebra]:


<pre><span class=hs-linenum>126: </span><a class=annot href="#"><span class=annottext>() -&gt; {VV : () | Set_mem 2 (RangeSet.rng 1 3)}</span><span class='hs-definition'>test1</span></a> <span class='hs-conid'>()</span>
<span class=hs-linenum>127: </span>  <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_mem x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>member</span> <span class='hs-num'>2</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-num'>1</span> <span class='hs-num'>3</span><span class='hs-layout'>)</span>
<span class=hs-linenum>128: </span>      <span class='hs-comment'>-- by unfolding `rng 1 3`</span>
<span class=hs-linenum>129: </span>  <span class='hs-varop'>===</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_mem x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>member</span> <span class='hs-num'>2</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : (Set Int) | v == Set_cup x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>union</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(Set Int)</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>singleton</span> <span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-num'>2</span> <span class='hs-num'>3</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>130: </span>      <span class='hs-comment'>-- by unfolding `rng 2 3`</span>
<span class=hs-linenum>131: </span>  <span class='hs-varop'>===</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_mem x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>member</span> <span class='hs-num'>2</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : (Set Int) | v == Set_cup x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>union</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(Set Int)</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>singleton</span> <span class='hs-num'>1</span><span class='hs-layout'>)</span>
<span class=hs-linenum>132: </span>                          <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : (Set Int) | v == Set_cup x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>union</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(Set Int)</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>singleton</span> <span class='hs-num'>2</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-num'>3</span> <span class='hs-num'>3</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>133: </span>      <span class='hs-comment'>-- by set-theory</span>
<span class=hs-linenum>134: </span>  <span class='hs-varop'>===</span> <span class='hs-conid'>True</span>
<span class=hs-linenum>135: </span>  <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
</pre>

the "proof" uses two library operators:

- `e1 === e2` is an [implicit equality][lh-imp-eq]
  that checks `e1` is indeed equal to `e2` after
  **unfolding functions at most once**, and returns
  a term that equals `e1` and `e2`, and

- `e *** QED` [converts any term][lh-qed] `e`
  into a proof.

The first two steps of `test1`, simply unfold `rng`
and the final step uses the SMT solver's
decision procedure for sets to check equalities
over set operations like `S.union`, `S.singleton`
and `S.member`.

Reusing Proofs
--------------

Next, lets check that:


<pre><span class=hs-linenum>160: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>test2</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>()</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{ S.member 2 (rng 0 3) }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>161: </span><a class=annot href="#"><span class=annottext>() -&gt; {VV : () | Set_mem 2 (RangeSet.rng 0 3)}</span><span class='hs-definition'>test2</span></a> <span class='hs-conid'>()</span>
<span class=hs-linenum>162: </span>  <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_mem x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>member</span> <span class='hs-num'>2</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-num'>0</span> <span class='hs-num'>3</span><span class='hs-layout'>)</span>
<span class=hs-linenum>163: </span>      <span class='hs-comment'>-- by unfolding and set-theory</span>
<span class=hs-linenum>164: </span>  <span class='hs-varop'>===</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>Bool</span><span class='hs-num'>2</span></a> <a class=annot href="#"><span class=annottext>x1:Integer -&gt; x2:Integer -&gt; {v : Bool | v &lt;=&gt; x1 == x2}</span><span class='hs-varop'>==</span></a> <span class='hs-num'>0</span> <a class=annot href="#"><span class=annottext>{v : x1:Bool -&gt; x2:Bool -&gt; {v : Bool | v &lt;=&gt; x1
                                             || x2} | v == GHC.Classes.||}</span><span class='hs-varop'>||</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_mem x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>member</span> <span class='hs-num'>2</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-num'>1</span> <span class='hs-num'>3</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>165: </span>      <span class='hs-comment'>-- by re-using test1 as a lemma</span>
<span class=hs-linenum>166: </span>  <span class='hs-varop'>==?</span> <span class='hs-conid'>True</span> <span class='hs-varop'>?</span> <a class=annot href="#"><span class=annottext>{v : () -&gt; {v : () | Set_mem 2 (RangeSet.rng 1 3)} | v == RangeSet.test1}</span><span class='hs-varid'>test1</span></a> <span class='hs-conid'>()</span>
<span class=hs-linenum>167: </span>  <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
</pre>

We could do the proof by unfolding in
the equational style. However, `test1`
already establishes that `S.member 2 (rng 1 3)`
and we can reuse this fact using:

- `e1 ==? e2 ? pf` an [explicit equality][lh-exp-eq]
  which checks that `e1` equals `e2` _because of_ the
  extra facts asserted by the `Proof` named `pf`
  (in addition to unfolding functions at most once)
  and returns a term that equals both `e1` and `e2`.

Proof by Logical Evaluation
---------------------------

Equational proofs like `test1` and `test2`
often have long chains of calculations that
can be tedious to spell out. Fortunately, we
taught LH a new trick called
**Proof by Logical Evaluation** (PLE) that
optionally shifts the burden of performing
those calculations onto the machine. For example,
PLE completely automates the above proofs:


<pre><span class=hs-linenum>194: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>test1_ple</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>()</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{ S.member 2 (rng 1 3) }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>195: </span><a class=annot href="#"><span class=annottext>() -&gt; {VV : () | Set_mem 2 (RangeSet.rng 1 3)}</span><span class='hs-definition'>test1_ple</span></a> <span class='hs-conid'>()</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>196: </span>
<span class=hs-linenum>197: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>test2_ple</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>()</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{ S.member 2 (rng 0 3) }</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>198: </span><a class=annot href="#"><span class=annottext>() -&gt; {VV : () | Set_mem 2 (RangeSet.rng 0 3)}</span><span class='hs-definition'>test2_ple</span></a> <span class='hs-conid'>()</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span>
</pre>

**Be Warned!** While automation is cool,
it can be *very* helpful to first write
out all the steps of an equational proof,
at least while building up intuition.


Proof by Induction
------------------

At this point, we have enough tools to start proving some
interesting facts about range-sets. For example, if `x`
is _outside_ the range `i..j` then it does not belong in
`rng i j`:


<pre><span class=hs-linenum>216: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>lem_mem</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyword'>{x &lt; i || j &lt;= x}</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>217: </span>                 <span class='hs-keyword'>{ not (S.member x (rng i j)) }</span> <span class='hs-varop'>/</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>j</span> <span class='hs-comment'>-</span> <span class='hs-varid'>i</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>218: </span>  <span class='hs-keyword'>@-}</span>
</pre>

We will prove the above ["by induction"][tag-induction].
A confession: I always had trouble understanding what
exactly _proof by induction_ really meant. Why was it
it ok to "do" induction on one thing but not another?

**Induction is Recursion**

Fortunately, with LH, induction is just recursion. That is,

1. We can **recursively** use the same theorem we
   are trying to prove, but

2. We must make sure that the recursive function/proof
   **terminates**.

The proof makes this clear:


<pre><span class=hs-linenum>239: </span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; x3:{v : Int | v &lt; x1
                                  || x2 &lt;= v} -&gt; {VV : () | not (Set_mem x3 (RangeSet.rng x1 x2))}</span><span class='hs-definition'>lem_mem</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>j</span></a> <a class=annot href="#"><span class=annottext>{v : Int | v &lt; i
           || j &lt;= v}</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>240: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; i &gt;= j}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &gt;= x2}</span><span class='hs-varop'>&gt;=</span></a> <span class='hs-varid'>j</span>
<span class=hs-linenum>241: </span>      <span class='hs-comment'>-- BASE CASE</span>
<span class=hs-linenum>242: </span>  <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>{v : x1:Bool -&gt; {v : Bool | v &lt;=&gt; not x1} | v == GHC.Classes.not}</span><span class='hs-varid'>not</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_mem x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>member</span> <span class='hs-varid'>x</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-varid'>i</span> <span class='hs-varid'>j</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>243: </span>      <span class='hs-comment'>-- by unfolding</span>
<span class=hs-linenum>244: </span>  <span class='hs-varop'>===</span> <a class=annot href="#"><span class=annottext>{v : x1:Bool -&gt; {v : Bool | v &lt;=&gt; not x1} | v == GHC.Classes.not}</span><span class='hs-varid'>not</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_mem x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>member</span> <span class='hs-varid'>x</span> <span class='hs-conid'>S</span><span class='hs-varop'>.</span><span class='hs-varid'>empty</span><span class='hs-layout'>)</span>
<span class=hs-linenum>245: </span>      <span class='hs-comment'>-- by set-theory</span>
<span class=hs-linenum>246: </span>  <span class='hs-varop'>===</span> <span class='hs-conid'>True</span> <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
<span class=hs-linenum>247: </span>
<span class=hs-linenum>248: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; i &lt; j}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>j</span>
<span class=hs-linenum>249: </span>      <span class='hs-comment'>-- INDUCTIVE CASE</span>
<span class=hs-linenum>250: </span>  <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>{v : x1:Bool -&gt; {v : Bool | v &lt;=&gt; not x1} | v == GHC.Classes.not}</span><span class='hs-varid'>not</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_mem x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>member</span> <span class='hs-varid'>x</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-varid'>i</span> <span class='hs-varid'>j</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>251: </span>      <span class='hs-comment'>-- by unfolding</span>
<span class=hs-linenum>252: </span>  <span class='hs-varop'>===</span> <a class=annot href="#"><span class=annottext>{v : x1:Bool -&gt; {v : Bool | v &lt;=&gt; not x1} | v == GHC.Classes.not}</span><span class='hs-varid'>not</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_mem x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>member</span> <span class='hs-varid'>x</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : (Set Int) | v == Set_cup x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>union</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : (Set Int) | v == Set_sng i}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>singleton</span> <span class='hs-varid'>i</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varid'>j</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>253: </span>      <span class='hs-comment'>-- by set-theory</span>
<span class=hs-linenum>254: </span>  <span class='hs-varop'>===</span> <a class=annot href="#"><span class=annottext>{v : x1:Bool -&gt; {v : Bool | v &lt;=&gt; not x1} | v == GHC.Classes.not}</span><span class='hs-varid'>not</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_mem x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>member</span> <span class='hs-varid'>x</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i</span></a><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varid'>j</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>255: </span>      <span class='hs-comment'>-- by "induction hypothesis"</span>
<span class=hs-linenum>256: </span>  <span class='hs-varop'>==?</span> <span class='hs-conid'>True</span> <span class='hs-varop'>?</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; x3:{v : Int | v &lt; x1
                                  || x2 &lt;= v} -&gt; {VV : () | not (Set_mem x3 (RangeSet.rng x1 x2))}</span><span class='hs-varid'>lem_mem</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varid'>j</span> <span class='hs-varid'>x</span> <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
</pre>

There are two cases.

- **Base Case:** As `i >= j`, we know `rng i j` is empty, so `x`
  cannot be in it.

- **Inductive Case** As `i < j` we can unfold `rng i j` and
  then _recursively call_ `lem_mem (i+1) j` to obtain the fact
  that `x` cannot be in `i+1..j` to complete the proof.

LH automatically checks that the proof:

1. **Accounts for all cases**, as otherwise the
   function is _not total_ i.e. like the `head` function
   which is only defined on non-empty lists.
   (Try deleting a case at the [demo][demo] to see what happens.)

2. **Terminates**, as otherwise the induction
   is bogus, or in math-speak, not _well-founded_.
   We use the [explicit termination metric][lh-termination]
   `/ [j-i]` as a hint to tell LH that in each recursive call,
   the size of the interval `j-i` shrinks and is
   always non-negative. LH checks that is indeed the case,
   ensuring that we have a legit proof by induction.

**Proof by Evaluation**

Once you get the hang of the above style, you get tired
of spelling out all the details. Logical evaluation lets
us eliminate all the boring calculational steps, leaving
the essential bits: the recursive (inductive) skeleton


<pre><span class=hs-linenum>291: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>lem_mem_ple</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyword'>{x &lt; i || j &lt;= x}</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>292: </span>                     <span class='hs-keyword'>{not (S.member x (rng i j))}</span> <span class='hs-varop'>/</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>j</span><span class='hs-comment'>-</span><span class='hs-varid'>i</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>293: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>294: </span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; x3:{v : Int | v &lt; x1
                                  || x2 &lt;= v} -&gt; {VV : () | not (Set_mem x3 (RangeSet.rng x1 x2))}</span><span class='hs-definition'>lem_mem_ple</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>j</span></a> <a class=annot href="#"><span class=annottext>{v : Int | v &lt; i
           || j &lt;= v}</span><span class='hs-varid'>x</span></a>
<span class=hs-linenum>295: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; i &gt;= j}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &gt;= x2}</span><span class='hs-varop'>&gt;=</span></a> <span class='hs-varid'>j</span> <span class='hs-keyglyph'>=</span>  <span class='hs-conid'>()</span>
<span class=hs-linenum>296: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; i &lt; j}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>j</span>  <span class='hs-keyglyph'>=</span>  <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; x3:{v : Int | v &lt; x1
                                  || x2 &lt;= v} -&gt; {VV : () | not (Set_mem x3 (RangeSet.rng x1 x2))}</span><span class='hs-varid'>lem_mem_ple</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varid'>j</span> <span class='hs-varid'>x</span>
</pre>

The above is just `lem_mem` sans the
(PLE-synthesized) intermediate equalities.


Disjointness
------------

We say that two sets are _disjoint_ if their `intersection` is `empty`:


<pre><span class=hs-linenum>309: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>inline</span> <span class='hs-varid'>disjoint</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>310: </span><span class='hs-definition'>disjoint</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>S</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>S</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>311: </span><a class=annot href="#"><span class=annottext>x1:(Set Int) -&gt; x2:(Set Int) -&gt; {VV : Bool | VV &lt;=&gt; Set_cap x1 x2 == Set_empty 0}</span><span class='hs-definition'>disjoint</span></a> <a class=annot href="#"><span class=annottext>(Set Int)</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>(Set Int)</span><span class='hs-varid'>b</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : (Set Int) | v == Set_cap x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>intersection</span> <span class='hs-varid'>a</span> <span class='hs-varid'>b</span> <a class=annot href="#"><span class=annottext>x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; x1 == x2}</span><span class='hs-varop'>==</span></a> <span class='hs-conid'>S</span><span class='hs-varop'>.</span><span class='hs-varid'>empty</span>
</pre>

Lets prove that two intervals are disjoint if
the first _ends_ before the second _begins_:


<pre><span class=hs-linenum>318: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>lem_disj</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j1</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-keyword'>{j1 &lt;= i2}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j2</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>319: </span>                  <span class='hs-keyword'>{disjoint (rng i1 j1) (rng i2 j2)}</span> <span class='hs-varop'>/</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>j2</span><span class='hs-comment'>-</span><span class='hs-varid'>i2</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>320: </span>  <span class='hs-keyword'>@-}</span>
</pre>

This proof goes "by induction" on the size of
the second interval, i.e. `j2-i2`:


<pre><span class=hs-linenum>327: </span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; x3:{i2 : Int | x2 &lt;= i2} -&gt; x4:Int -&gt; {VV : () | Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x3 x4) == Set_empty 0}</span><span class='hs-definition'>lem_disj</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i1</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>j1</span></a> <a class=annot href="#"><span class=annottext>{i2 : Int | j1 &lt;= i2}</span><span class='hs-varid'>i2</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>j2</span></a>
<span class=hs-linenum>328: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; i2 &gt;= j2}</span><span class='hs-varid'>i2</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &gt;= x2}</span><span class='hs-varop'>&gt;=</span></a> <span class='hs-varid'>j2</span>
<span class=hs-linenum>329: </span>      <span class='hs-comment'>-- Base CASE</span>
<span class=hs-linenum>330: </span>  <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>{v : x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_cap x1 x2 == Set_empty 0} | v == RangeSet.disjoint}</span><span class='hs-varid'>disjoint</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-varid'>i1</span> <span class='hs-varid'>j1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-varid'>i2</span> <span class='hs-varid'>j2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>331: </span>      <span class='hs-comment'>-- by unfolding</span>
<span class=hs-linenum>332: </span>  <span class='hs-varop'>===</span> <a class=annot href="#"><span class=annottext>{v : x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_cap x1 x2 == Set_empty 0} | v == RangeSet.disjoint}</span><span class='hs-varid'>disjoint</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-varid'>i1</span> <span class='hs-varid'>j1</span><span class='hs-layout'>)</span> <span class='hs-conid'>S</span><span class='hs-varop'>.</span><span class='hs-varid'>empty</span>
<span class=hs-linenum>333: </span>      <span class='hs-comment'>-- by set-theory</span>
<span class=hs-linenum>334: </span>  <span class='hs-varop'>===</span> <span class='hs-conid'>True</span>
<span class=hs-linenum>335: </span>  <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
<span class=hs-linenum>336: </span>
<span class=hs-linenum>337: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; i2 &lt; j2}</span><span class='hs-varid'>i2</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>j2</span>
<span class=hs-linenum>338: </span>      <span class='hs-comment'>-- Inductive CASE</span>
<span class=hs-linenum>339: </span>  <span class='hs-keyglyph'>=</span>   <a class=annot href="#"><span class=annottext>{v : x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_cap x1 x2 == Set_empty 0} | v == RangeSet.disjoint}</span><span class='hs-varid'>disjoint</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-varid'>i1</span> <span class='hs-varid'>j1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-varid'>i2</span> <span class='hs-varid'>j2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>340: </span>      <span class='hs-comment'>-- by unfolding</span>
<span class=hs-linenum>341: </span>  <span class='hs-varop'>===</span> <a class=annot href="#"><span class=annottext>{v : x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_cap x1 x2 == Set_empty 0} | v == RangeSet.disjoint}</span><span class='hs-varid'>disjoint</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-varid'>i1</span> <span class='hs-varid'>j1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : (Set Int) | v == Set_cup x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>union</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : (Set Int) | v == Set_sng i2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>singleton</span> <span class='hs-varid'>i2</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; {v : (Set Int) | v == RangeSet.rng x1 x2
                                          &amp;&amp; v == (if x1 &lt; x2 then Set_cup (Set_sng x1) (RangeSet.rng (x1 + 1) x2) else Set_empty 0)} | v == RangeSet.rng}</span><span class='hs-varid'>rng</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i2</span></a><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varid'>j2</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>342: </span>      <span class='hs-comment'>-- by induction and lem_mem</span>
<span class=hs-linenum>343: </span>  <span class='hs-varop'>==?</span> <span class='hs-conid'>True</span> <span class='hs-varop'>?</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; x3:{v : Int | v &lt; x1
                                       || x2 &lt;= v} -&gt; {v : () | not (Set_mem x3 (RangeSet.rng x1 x2))} | v == RangeSet.lem_mem}</span><span class='hs-varid'>lem_mem</span></a> <span class='hs-varid'>i1</span> <span class='hs-varid'>j1</span> <span class='hs-varid'>i2</span> <a class=annot href="#"><span class=annottext>{v : () -&gt; () -&gt; () | v == Language.Haskell.Liquid.NewProofCombinators.&amp;&amp;&amp;}</span><span class='hs-varop'>&amp;&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; x3:{i2 : Int | x2 &lt;= i2} -&gt; x4:Int -&gt; {VV : () | Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x3 x4) == Set_empty 0}</span><span class='hs-varid'>lem_disj</span></a> <span class='hs-varid'>i1</span> <span class='hs-varid'>j1</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i2</span></a><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varid'>j2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>344: </span>  <span class='hs-varop'>***</span> <span class='hs-conid'>QED</span>
</pre>

Here, the operator `pf1 &&& pf2` conjoins the
two facts asserted by `pf1` and `pf2`.

Again, we can get PLE to do the boring calculations:


<pre><span class=hs-linenum>353: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>lem_disj_ple</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j1</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-keyword'>{j1 &lt;= i2}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j2</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>354: </span>                      <span class='hs-keyword'>{disjoint (rng i1 j1) (rng i2 j2)}</span> <span class='hs-varop'>/</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>j2</span><span class='hs-comment'>-</span><span class='hs-varid'>i2</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>355: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>356: </span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; x3:{i2 : Int | x2 &lt;= i2} -&gt; x4:Int -&gt; {VV : () | Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x3 x4) == Set_empty 0}</span><span class='hs-definition'>lem_disj_ple</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i1</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>j1</span></a> <a class=annot href="#"><span class=annottext>{i2 : Int | j1 &lt;= i2}</span><span class='hs-varid'>i2</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>j2</span></a>
<span class=hs-linenum>357: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; i2 &gt;= j2}</span><span class='hs-varid'>i2</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &gt;= x2}</span><span class='hs-varop'>&gt;=</span></a> <span class='hs-varid'>j2</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>358: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; i2 &lt; j2}</span><span class='hs-varid'>i2</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a>  <span class='hs-varid'>j2</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; x3:{v : Int | v &lt; x1
                                       || x2 &lt;= v} -&gt; {v : () | not (Set_mem x3 (RangeSet.rng x1 x2))} | v == RangeSet.lem_mem}</span><span class='hs-varid'>lem_mem</span></a> <span class='hs-varid'>i1</span> <span class='hs-varid'>j1</span> <span class='hs-varid'>i2</span> <a class=annot href="#"><span class=annottext>{v : () -&gt; () -&gt; () | v == Language.Haskell.Liquid.NewProofCombinators.&amp;&amp;&amp;}</span><span class='hs-varop'>&amp;&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; x3:{i2 : Int | x2 &lt;= i2} -&gt; x4:Int -&gt; {VV : () | Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x3 x4) == Set_empty 0}</span><span class='hs-varid'>lem_disj_ple</span></a> <span class='hs-varid'>i1</span> <span class='hs-varid'>j1</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i2</span></a><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a><span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varid'>j2</span>
</pre>


Splitting Intervals
-------------------

Finally, we can establish the **splitting property**
of an interval `i..j`, that is, given some `x` that lies
between `i` and `j` we can **split** `i..j` into `i..x`
and `x..j`. We define a predicate that a set `s` can
be split into `a` and `b` as:


<pre><span class=hs-linenum>372: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>inline</span> <span class='hs-varid'>split</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>373: </span><span class='hs-definition'>split</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>S</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>S</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>S</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>374: </span><a class=annot href="#"><span class=annottext>x1:(Set Int) -&gt; x2:(Set Int) -&gt; x3:(Set Int) -&gt; {VV : Bool | VV &lt;=&gt; x1 == Set_cup x2 x3
                                                                    &amp;&amp; Set_cap x2 x3 == Set_empty 0}</span><span class='hs-definition'>split</span></a> <a class=annot href="#"><span class=annottext>(Set Int)</span><span class='hs-varid'>s</span></a> <a class=annot href="#"><span class=annottext>(Set Int)</span><span class='hs-varid'>a</span></a> <a class=annot href="#"><span class=annottext>(Set Int)</span><span class='hs-varid'>b</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>Bool</span><span class='hs-varid'>s</span></a> <a class=annot href="#"><span class=annottext>x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; x1 == x2}</span><span class='hs-varop'>==</span></a> <a class=annot href="#"><span class=annottext>x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : (Set Int) | v == Set_cup x1 x2}</span><span class='hs-conid'>S</span></a><span class='hs-varop'>.</span><span class='hs-varid'>union</span> <span class='hs-varid'>a</span> <span class='hs-varid'>b</span> <a class=annot href="#"><span class=annottext>{v : x1:Bool -&gt; x2:Bool -&gt; {v : Bool | v &lt;=&gt; x1
                                             &amp;&amp; x2} | v == GHC.Classes.&amp;&amp;}</span><span class='hs-varop'>&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>{v : x1:(Set Int) -&gt; x2:(Set Int) -&gt; {v : Bool | v &lt;=&gt; Set_cap x1 x2 == Set_empty 0} | v == RangeSet.disjoint}</span><span class='hs-varid'>disjoint</span></a> <span class='hs-varid'>a</span> <span class='hs-varid'>b</span>
</pre>

We can now state and prove the **splitting property** as:


<pre><span class=hs-linenum>380: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>lem_split</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>x</span><span class='hs-conop'>:</span><span class='hs-keyword'>{i &lt;= x}</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j</span><span class='hs-conop'>:</span><span class='hs-keyword'>{x &lt;= j}</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>381: </span>                   <span class='hs-keyword'>{split (rng i j) (rng i x) (rng x j)}</span> <span class='hs-varop'>/</span> <span class='hs-keyglyph'>[</span><span class='hs-varid'>x</span><span class='hs-comment'>-</span><span class='hs-varid'>i</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>382: </span>  <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>383: </span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:{v : Int | x1 &lt;= v} -&gt; x3:{j : Int | x2 &lt;= j} -&gt; {VV : () | RangeSet.rng x1 x3 == Set_cup (RangeSet.rng x1 x2) (RangeSet.rng x2 x3)
                                                                         &amp;&amp; Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x2 x3) == Set_empty 0}</span><span class='hs-definition'>lem_split</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>{v : Int | i &lt;= v}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>{j : Int | x &lt;= j}</span><span class='hs-varid'>t</span></a>
<span class=hs-linenum>384: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; i == x}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 == x2}</span><span class='hs-varop'>==</span></a> <span class='hs-varid'>x</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>385: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; i &lt; x}</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a>  <span class='hs-varid'>x</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:{v : Int | x1 &lt;= v} -&gt; x3:{j : Int | x2 &lt;= j} -&gt; {VV : () | RangeSet.rng x1 x3 == Set_cup (RangeSet.rng x1 x2) (RangeSet.rng x2 x3)
                                                                         &amp;&amp; Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x2 x3) == Set_empty 0}</span><span class='hs-varid'>lem_split</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == x1 + x2}</span><span class='hs-varop'>+</span></a> <span class='hs-num'>1</span><span class='hs-layout'>)</span> <span class='hs-varid'>x</span> <span class='hs-varid'>t</span> <a class=annot href="#"><span class=annottext>{v : () -&gt; () -&gt; () | v == Language.Haskell.Liquid.NewProofCombinators.&amp;&amp;&amp;}</span><span class='hs-varop'>&amp;&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; x3:{v : Int | v &lt; x1
                                       || x2 &lt;= v} -&gt; {v : () | not (Set_mem x3 (RangeSet.rng x1 x2))} | v == RangeSet.lem_mem}</span><span class='hs-varid'>lem_mem</span></a> <span class='hs-varid'>x</span> <span class='hs-varid'>t</span> <span class='hs-varid'>i</span>
</pre>

(We're using PLE here quite aggressively, can _you_ work out the equational proof?)


Set Operations
--------------

The splitting abstraction is a wonderful hammer that lets us
break higher-level proofs into the bite sized pieces suitable
for the SMT solver's decision procedures.

**Subset**

An interval `i1..j1` is _enclosed by_ `i2..j2`
if `i2 <= i1 < j1 <= j2`. Lets verify that the
range-set of an interval is **contained** in
that of an enclosing one.


<pre><span class=hs-linenum>406: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>lem_sub</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j1</span><span class='hs-conop'>:</span><span class='hs-keyword'>{i1 &lt; j1}</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>407: </span>               <span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j2</span><span class='hs-conop'>:</span><span class='hs-keyword'>{i2 &lt; j2 &amp;&amp; i2 &lt;= i1 &amp;&amp; j1 &lt;= j2 }</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>408: </span>                 <span class='hs-keyword'>{ S.isSubsetOf (rng i1 j1) (rng i2 j2) }</span>
<span class=hs-linenum>409: </span>  <span class='hs-keyword'>@-}</span>
</pre>

Here's a "proof-by-picture". We can split the
larger interval `i2..j2` into smaller pieces,
`i2..i1`, `i1..j1` and `j1..j2` one of which
is the `i1..j1`, thereby completing the proof:

<br>
<div class="row">
  <div class="col-lg-2"></div>
  <div class="col-lg-8">
  ![`lem_sub` a proof by picture](../static/img/lem_sub.png "lem_sub proof by picture")
  </div>
  <div class="col-lg-2"></div>
</div>
<br>

The intuition represented by the picture can distilled
into the following proof, that invokes `lem_split` to
carve `i2..j2` into the relevant sub-intervals:


<pre><span class=hs-linenum>432: </span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:{j1 : Int | x1 &lt; j1} -&gt; x3:Int -&gt; x4:{j2 : Int | x3 &lt; j2
                                                              &amp;&amp; x3 &lt;= x1
                                                              &amp;&amp; x2 &lt;= j2} -&gt; {VV : () | Set_sub (RangeSet.rng x1 x2) (RangeSet.rng x3 x4)}</span><span class='hs-definition'>lem_sub</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i1</span></a> <a class=annot href="#"><span class=annottext>{j1 : Int | i1 &lt; j1}</span><span class='hs-varid'>j1</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i2</span></a> <a class=annot href="#"><span class=annottext>{j2 : Int | i2 &lt; j2
            &amp;&amp; i2 &lt;= i1
            &amp;&amp; j1 &lt;= j2}</span><span class='hs-varid'>j2</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt;= v} -&gt; x3:{v : Int | x2 &lt;= v} -&gt; {v : () | RangeSet.rng x1 x3 == Set_cup (RangeSet.rng x1 x2) (RangeSet.rng x2 x3)
                                                                             &amp;&amp; Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x2 x3) == Set_empty 0} | v == RangeSet.lem_split}</span><span class='hs-varid'>lem_split</span></a> <span class='hs-varid'>i2</span> <span class='hs-varid'>i1</span> <span class='hs-varid'>j2</span> <a class=annot href="#"><span class=annottext>{v : () -&gt; () -&gt; () | v == Language.Haskell.Liquid.NewProofCombinators.&amp;&amp;&amp;}</span><span class='hs-varop'>&amp;&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt;= v} -&gt; x3:{v : Int | x2 &lt;= v} -&gt; {v : () | RangeSet.rng x1 x3 == Set_cup (RangeSet.rng x1 x2) (RangeSet.rng x2 x3)
                                                                             &amp;&amp; Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x2 x3) == Set_empty 0} | v == RangeSet.lem_split}</span><span class='hs-varid'>lem_split</span></a> <span class='hs-varid'>i1</span> <span class='hs-varid'>j1</span> <span class='hs-varid'>j2</span>
</pre>

**Union**

An interval `i1..j1` _overlaps_ `i2..j2`
if `i1 <= j2 <= i2`, that is, if the latter
ends somewhere inside the former.
The same splitting hammer lets us compute
the union of two overlapping intervals
simply by picking the interval defined
by the _endpoints_.


<pre><span class=hs-linenum>446: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>lem_union</span> <span class='hs-keyglyph'>::</span>
<span class=hs-linenum>447: </span>      <span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j1</span><span class='hs-conop'>:</span><span class='hs-keyword'>{i1 &lt; j1}</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>448: </span>      <span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j2</span><span class='hs-conop'>:</span><span class='hs-keyword'>{i2 &lt; j2 &amp;&amp; i1 &lt;= j2 &amp;&amp; j2 &lt;= j1 }</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>449: </span>        <span class='hs-keyword'>{ rng (min i1 i2) j1 = S.union (rng i1 j1) (rng i2 j2) }</span>
<span class=hs-linenum>450: </span>  <span class='hs-keyword'>@-}</span>
</pre>

<br>
<div class="row">
  <div class="col-lg-2"></div>
  <div class="col-lg-8">
  ![`lem_union` a proof by picture](../static/img/lem_union.png "lem_union proof by picture")
  </div>
  <div class="col-lg-2"></div>
</div>
<br>

The pictorial proof illustrates the two cases:

1. `i1..j1` encloses `i2..j2`; here the union is just `i1..j1`,

2. `i1..j1` only overlaps `i1..j1`; here the union is `i2..j1` which
   can be split into `i2..i1`, `i1..j2` and `j2..j1` which are exactly
   the union of the intervals `i1..j1` and `i2..j2`.

Again, we render the picture into a formal proof as:


<pre><span class=hs-linenum>474: </span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:{j1 : Int | x1 &lt; j1} -&gt; x3:Int -&gt; x4:{j2 : Int | x3 &lt; j2
                                                              &amp;&amp; x1 &lt;= j2
                                                              &amp;&amp; j2 &lt;= x2} -&gt; {VV : () | RangeSet.rng (RangeSet.min x1 x3) x2 == Set_cup (RangeSet.rng x1 x2) (RangeSet.rng x3 x4)}</span><span class='hs-definition'>lem_union</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i1</span></a> <a class=annot href="#"><span class=annottext>{j1 : Int | i1 &lt; j1}</span><span class='hs-varid'>j1</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i2</span></a> <a class=annot href="#"><span class=annottext>{j2 : Int | i2 &lt; j2
            &amp;&amp; i1 &lt;= j2
            &amp;&amp; j2 &lt;= j1}</span><span class='hs-varid'>j2</span></a>
<span class=hs-linenum>475: </span>  <span class='hs-comment'>-- i1..j1 encloses i2..j2</span>
<span class=hs-linenum>476: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; i1 &lt; i2}</span><span class='hs-varid'>i1</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>i2</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; x3:Int -&gt; x4:{v : Int | x3 &lt; v
                                                                &amp;&amp; x3 &lt;= x1
                                                                &amp;&amp; x2 &lt;= v} -&gt; {v : () | Set_sub (RangeSet.rng x1 x2) (RangeSet.rng x3 x4)} | v == RangeSet.lem_sub}</span><span class='hs-varid'>lem_sub</span></a> <span class='hs-varid'>i2</span> <span class='hs-varid'>j2</span> <span class='hs-varid'>i1</span> <span class='hs-varid'>j1</span>
<span class=hs-linenum>477: </span>  <span class='hs-comment'>-- i1..j1 overlaps i2..j2</span>
<span class=hs-linenum>478: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt;= v} -&gt; x3:{v : Int | x2 &lt;= v} -&gt; {v : () | RangeSet.rng x1 x3 == Set_cup (RangeSet.rng x1 x2) (RangeSet.rng x2 x3)
                                                                             &amp;&amp; Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x2 x3) == Set_empty 0} | v == RangeSet.lem_split}</span><span class='hs-varid'>lem_split</span></a> <span class='hs-varid'>i2</span> <span class='hs-varid'>i1</span> <span class='hs-varid'>j1</span>
<span class=hs-linenum>479: </span>            <a class=annot href="#"><span class=annottext>{v : () -&gt; () -&gt; () | v == Language.Haskell.Liquid.NewProofCombinators.&amp;&amp;&amp;}</span><span class='hs-varop'>&amp;&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt;= v} -&gt; x3:{v : Int | x2 &lt;= v} -&gt; {v : () | RangeSet.rng x1 x3 == Set_cup (RangeSet.rng x1 x2) (RangeSet.rng x2 x3)
                                                                             &amp;&amp; Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x2 x3) == Set_empty 0} | v == RangeSet.lem_split}</span><span class='hs-varid'>lem_split</span></a> <span class='hs-varid'>i1</span> <span class='hs-varid'>j2</span> <span class='hs-varid'>j1</span>
<span class=hs-linenum>480: </span>            <a class=annot href="#"><span class=annottext>{v : () -&gt; () -&gt; () | v == Language.Haskell.Liquid.NewProofCombinators.&amp;&amp;&amp;}</span><span class='hs-varop'>&amp;&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt;= v} -&gt; x3:{v : Int | x2 &lt;= v} -&gt; {v : () | RangeSet.rng x1 x3 == Set_cup (RangeSet.rng x1 x2) (RangeSet.rng x2 x3)
                                                                             &amp;&amp; Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x2 x3) == Set_empty 0} | v == RangeSet.lem_split}</span><span class='hs-varid'>lem_split</span></a> <span class='hs-varid'>i2</span> <span class='hs-varid'>i1</span> <span class='hs-varid'>j2</span>
</pre>

**Intersection**

Finally, we check that the intersection of two overlapping intervals
is given by their _inner-points_.


<pre><span class=hs-linenum>489: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>lem_intersect</span> <span class='hs-keyglyph'>::</span>
<span class=hs-linenum>490: </span>      <span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j1</span><span class='hs-conop'>:</span><span class='hs-keyword'>{i1 &lt; j1}</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>491: </span>      <span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-keyword'>_</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>j2</span><span class='hs-conop'>:</span><span class='hs-keyword'>{i2 &lt; j2 &amp;&amp; i1 &lt;= j2 &amp;&amp; j2 &lt;= j1 }</span> <span class='hs-keyglyph'>-&gt;</span>
<span class=hs-linenum>492: </span>        <span class='hs-keyword'>{rng (max i1 i2) j2 = S.intersection (rng i1 j1) (rng i2 j2)}</span>
<span class=hs-linenum>493: </span>  <span class='hs-keyword'>@-}</span>
</pre>

<br>
<div class="row">
  <div class="col-lg-2"></div>
  <div class="col-lg-8">
  ![`lem_intersect` a proof by picture](../static/img/lem_intersect.png "lem_intersect proof by picture")
  </div>
  <div class="col-lg-2"></div>
</div>
<br>

We have the same two cases as for `lem_union`

1. `i1..j1` encloses `i2..j2`; here the intersection is just `i2..j2`,

2. `i1..j1` only overlaps `i1..j1`; here the intersection is the
   _middle segment_ `i1..j2`, which we obtain by
   (a) _splitting_ `i1..j1` at `j2`,
   (b) _splitting_ `i2..j2` at `i1`,
   (c) _discarding_ the end segments which do not belong in the intersection.


<pre><span class=hs-linenum>517: </span><a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:{j1 : Int | x1 &lt; j1} -&gt; x3:Int -&gt; x4:{j2 : Int | x3 &lt; j2
                                                              &amp;&amp; x1 &lt;= j2
                                                              &amp;&amp; j2 &lt;= x2} -&gt; {VV : () | RangeSet.rng (RangeSet.max x1 x3) x4 == Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x3 x4)}</span><span class='hs-definition'>lem_intersect</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i1</span></a> <a class=annot href="#"><span class=annottext>{j1 : Int | i1 &lt; j1}</span><span class='hs-varid'>j1</span></a> <a class=annot href="#"><span class=annottext>Int</span><span class='hs-varid'>i2</span></a> <a class=annot href="#"><span class=annottext>{j2 : Int | i2 &lt; j2
            &amp;&amp; i1 &lt;= j2
            &amp;&amp; j2 &lt;= j1}</span><span class='hs-varid'>j2</span></a>
<span class=hs-linenum>518: </span>  <span class='hs-comment'>-- i1..j1 encloses i2..j2</span>
<span class=hs-linenum>519: </span>  <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; i1 &lt; i2}</span><span class='hs-varid'>i1</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>i2</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; x3:Int -&gt; x4:{v : Int | x3 &lt; v
                                                                &amp;&amp; x3 &lt;= x1
                                                                &amp;&amp; x2 &lt;= v} -&gt; {v : () | Set_sub (RangeSet.rng x1 x2) (RangeSet.rng x3 x4)} | v == RangeSet.lem_sub}</span><span class='hs-varid'>lem_sub</span></a> <span class='hs-varid'>i2</span> <span class='hs-varid'>j2</span> <span class='hs-varid'>i1</span> <span class='hs-varid'>j1</span>
<span class=hs-linenum>520: </span>  <span class='hs-comment'>-- i1..j1 overlaps i2..j2</span>
<span class=hs-linenum>521: </span>  <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt;= v} -&gt; x3:{v : Int | x2 &lt;= v} -&gt; {v : () | RangeSet.rng x1 x3 == Set_cup (RangeSet.rng x1 x2) (RangeSet.rng x2 x3)
                                                                             &amp;&amp; Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x2 x3) == Set_empty 0} | v == RangeSet.lem_split}</span><span class='hs-varid'>lem_split</span></a> <span class='hs-varid'>i1</span> <span class='hs-varid'>j2</span> <span class='hs-varid'>j1</span>
<span class=hs-linenum>522: </span>            <a class=annot href="#"><span class=annottext>{v : () -&gt; () -&gt; () | v == Language.Haskell.Liquid.NewProofCombinators.&amp;&amp;&amp;}</span><span class='hs-varop'>&amp;&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt;= v} -&gt; x3:{v : Int | x2 &lt;= v} -&gt; {v : () | RangeSet.rng x1 x3 == Set_cup (RangeSet.rng x1 x2) (RangeSet.rng x2 x3)
                                                                             &amp;&amp; Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x2 x3) == Set_empty 0} | v == RangeSet.lem_split}</span><span class='hs-varid'>lem_split</span></a> <span class='hs-varid'>i2</span> <span class='hs-varid'>i1</span> <span class='hs-varid'>j2</span>
<span class=hs-linenum>523: </span>            <a class=annot href="#"><span class=annottext>{v : () -&gt; () -&gt; () | v == Language.Haskell.Liquid.NewProofCombinators.&amp;&amp;&amp;}</span><span class='hs-varop'>&amp;&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; x3:{v : Int | x2 &lt;= v} -&gt; x4:Int -&gt; {v : () | Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x3 x4) == Set_empty 0} | v == RangeSet.lem_disj}</span><span class='hs-varid'>lem_disj</span></a>  <span class='hs-varid'>i2</span> <span class='hs-varid'>i1</span> <span class='hs-varid'>i1</span> <span class='hs-varid'>j1</span>     <span class='hs-comment'>-- discard i2..i1</span>
<span class=hs-linenum>524: </span>            <a class=annot href="#"><span class=annottext>{v : () -&gt; () -&gt; () | v == Language.Haskell.Liquid.NewProofCombinators.&amp;&amp;&amp;}</span><span class='hs-varop'>&amp;&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:Int -&gt; x3:{v : Int | x2 &lt;= v} -&gt; x4:Int -&gt; {v : () | Set_cap (RangeSet.rng x1 x2) (RangeSet.rng x3 x4) == Set_empty 0} | v == RangeSet.lem_disj}</span><span class='hs-varid'>lem_disj</span></a>  <span class='hs-varid'>i2</span> <span class='hs-varid'>j2</span> <span class='hs-varid'>j2</span> <span class='hs-varid'>j1</span>     <span class='hs-comment'>-- discard j2..j1</span>
</pre>


Conclusions
-----------

Whew. That turned out a lot longer than I'd expected!

On the bright side, we saw how to:

1. _Specify_ the semantics of range-sets,
2. _Write_   equational proofs using plain Haskell code,
3. _Avoid_   boring proof steps using PLE,
4. _Verify_  key properties of operations on range-sets.

Next time we'll finish the series by showing how to use
the above lemmas to specify and verify the correctness
of [Breitner's implementation][nomeata-intervals].


<div class="hidden">

<pre><span class=hs-linenum>547: </span><span class='hs-comment'>--------------------------------------------------------------------------------</span>
<span class=hs-linenum>548: </span><span class='hs-comment'>-- | Some helper definitions</span>
<span class=hs-linenum>549: </span><span class='hs-comment'>--------------------------------------------------------------------------------</span>
<span class=hs-linenum>550: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reflect</span> <span class='hs-varid'>min</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>551: </span><span class='hs-definition'>min</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>552: </span><a class=annot href="#"><span class=annottext>(Ord a) =&gt;
x2:a -&gt; x3:a -&gt; {VV : a | VV == RangeSet.min x2 x3
                          &amp;&amp; VV == (if x2 &lt; x3 then x2 else x3)}</span><span class='hs-definition'>min</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; x &lt; y}</span><span class='hs-keyword'>if</span></a> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; x &lt; y}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; x2:a -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>y</span> <span class='hs-keyword'>then</span> <span class='hs-varid'>x</span> <span class='hs-keyword'>else</span> <span class='hs-varid'>y</span>
<span class=hs-linenum>553: </span>
<span class=hs-linenum>554: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>reflect</span> <span class='hs-varid'>max</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>555: </span><span class='hs-definition'>max</span> <span class='hs-keyglyph'>::</span> <span class='hs-layout'>(</span><span class='hs-conid'>Ord</span> <span class='hs-varid'>a</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>a</span>
<span class=hs-linenum>556: </span><a class=annot href="#"><span class=annottext>(Ord a) =&gt;
x2:a -&gt; x3:a -&gt; {VV : a | VV == RangeSet.max x2 x3
                          &amp;&amp; VV == (if x2 &lt; x3 then x3 else x2)}</span><span class='hs-definition'>max</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>a</span><span class='hs-varid'>y</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; x &lt; y}</span><span class='hs-keyword'>if</span></a> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; x &lt; y}</span><span class='hs-varid'>x</span></a> <a class=annot href="#"><span class=annottext>x1:a -&gt; x2:a -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>y</span> <span class='hs-keyword'>then</span> <span class='hs-varid'>y</span> <span class='hs-keyword'>else</span> <span class='hs-varid'>x</span>
<span class=hs-linenum>557: </span>
<span class=hs-linenum>558: </span><span class='hs-definition'>rng</span>         <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>S</span><span class='hs-varop'>.</span><span class='hs-conid'>Set</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>559: </span><span class='hs-definition'>test1</span>       <span class='hs-keyglyph'>::</span> <span class='hs-conid'>()</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>560: </span><span class='hs-definition'>test2</span>       <span class='hs-keyglyph'>::</span> <span class='hs-conid'>()</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>561: </span><span class='hs-definition'>test1_ple</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>()</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>562: </span><span class='hs-definition'>test2_ple</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>()</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>563: </span><span class='hs-definition'>lem_mem</span>      <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>564: </span><span class='hs-definition'>lem_mem_ple</span>  <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>565: </span><span class='hs-definition'>lem_sub</span>      <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>566: </span><span class='hs-definition'>lem_disj</span>     <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>567: </span><span class='hs-definition'>lem_disj_ple</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>568: </span><span class='hs-definition'>lem_split</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>569: </span>
<span class=hs-linenum>570: </span><span class='hs-definition'>lem_intersect</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>571: </span><span class='hs-definition'>lem_union</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>()</span>
<span class=hs-linenum>572: </span><span class='hs-comment'>-- tags/induction.html</span>
<span class=hs-linenum>573: </span>
</pre>
</div>

[splicing-1]:        2017-12-15-splitting-and-splicing-intervals-I.lhs/
[lh-termination]:    https://github.com/ucsd-progsys/liquidhaskell/blob/develop/README.md#explicit-termination-metrics
[lh-qed]:            https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/NewProofCombinators.hs#L65-L69
[lh-imp-eq]:         https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/NewProofCombinators.hs#L87-L96
[lh-exp-eq]:         https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/NewProofCombinators.hs#L98-L116
[bird-algebra]:      http://themattchan.com/docs/algprog.pdf
[demo]:              http://goto.ucsd.edu:8090/index.html#?demo=RangeSet.hs
[intersect-good]:    https://github.com/antalsz/hs-to-coq/blob/8f84d61093b7be36190142c795d6cd4496ef5aed/examples/intervals/Proofs.v#L370-L439
[union-good]:        https://github.com/antalsz/hs-to-coq/blob/b7efc7a8dbacca384596fc0caf65e62e87ei2768/examples/intervals/Proofs_Function.v#L319-L382
[subtract-good]:     https://github.com/antalsz/hs-to-coq/blob/8f84d61093b7be36190142c795d6cd4496ef5aed/examples/intervals/Proofs.v#L565-L648
[tag-abs-ref]:       /tags/abstract-refinements.html
[tag-induction]:     /tags/induction.html
[tag-reflection]:    /tags/reflection.html
[hs-to-coq]:         https://github.com/antalsz/hs-to-coq
[nomeata-intervals]: https://www.joachim-breitner.de/blog/734-Finding_bugs_in_Haskell_code_by_proving_it
