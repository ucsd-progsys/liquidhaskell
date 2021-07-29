---
layout: post
title: CSV Tables
date: 2013-10-10 16:12
comments: true
tags: measures
author: Ranjit Jhala
published: true 
demo: Csv.hs
---

Most demonstrations for verification techniques involve programs with complicated
invariants and properties. However, these methods can often be rather useful for
describing simple but important aspects of APIs or programs with more humble
goals. I saw a rather [nice example][shapeless-csv] of using Scala's
`Shapeless` library for preventing off-by-one errors in CSV processing
code. Here's the same, short, example rephrased with LiquidHaskell.

<!-- more -->


<pre><span class=hs-linenum>23: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>CSV</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>24: </span>
<span class=hs-linenum>25: </span><span class='hs-comment'>-- | Using LiquidHaskell for CSV lists</span>
<span class=hs-linenum>26: </span><span class='hs-comment'>-- c.f. <a href="http://www.reddit.com/r/scala/comments/1nhzi2/using_shapelesss_sized_type_to_eliminate_real/">http://www.reddit.com/r/scala/comments/1nhzi2/using_shapelesss_sized_type_to_eliminate_real/</a></span>
</pre>


The Type
--------

Suppose you wanted to represent *tables* as a list of comma-separated values.

For example, here's a table listing the articles and prices at the coffee shop
I'm sitting in right now:

<table border="1">
<tr>
<th>Item</th>
<th>Price</th>
</tr>
<tr>
<td>Espresso</td>
<td>2.25</td>
</tr>
<tr>
<td>Macchiato</td>
<td>2.75</td>
</tr>
<tr>
<td>Cappucino</td>
<td>3.35</td>
</tr>
<tr>
<td>Americano</td>
<td>2.25</td>
</tr>
</table>

You might represent this with a simple Haskell data type:


<pre><span class=hs-linenum>64: </span>
<span class=hs-linenum>65: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>CSV</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Csv</span> <span class='hs-layout'>{</span> <a class=annot href="#"><span class=annottext>(CSV.CSV) -&gt; [[(GHC.Types.Char)]]</span><span class='hs-varid'>headers</span></a> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>String</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>66: </span>               <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>(CSV.CSV) -&gt; [[[(GHC.Types.Char)]]]</span><span class='hs-varid'>rows</span></a>    <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>String</span><span class='hs-keyglyph'>]</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>67: </span>               <span class='hs-layout'>}</span>
</pre>

and now, the above table is just:


<pre><span class=hs-linenum>73: </span><a class=annot href="#"><span class=annottext>(CSV.CSV)</span><span class='hs-definition'>zumbarMenu</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:[[(GHC.Types.Char)]]
-&gt; [{VV : [[(GHC.Types.Char)]] | ((len VV) == (len x1))}]
-&gt; (CSV.CSV)</span><span class='hs-conid'>Csv</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a>  <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Item"</span></a>     <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Price"</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>74: </span>                 <span class='hs-keyglyph'>[</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Espresso"</span></a> <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"2.25"</span></a> <span class='hs-keyglyph'>]</span>  
<span class=hs-linenum>75: </span>                 <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Macchiato"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"2.75"</span></a> <span class='hs-keyglyph'>]</span>
<span class=hs-linenum>76: </span>                 <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Cappucino"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"3.35"</span></a> <span class='hs-keyglyph'>]</span>
<span class=hs-linenum>77: </span>                 <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Americano"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"2.25"</span></a> <span class='hs-keyglyph'>]</span>
<span class=hs-linenum>78: </span>                 <span class='hs-keyglyph'>]</span>
</pre>

The Errors 
----------

Our `CSV` type supports tables with an arbitrary number of `headers` and
`rows` but of course, we'd like to ensure that each `row` has data for *each*
header, that is, we don't end up with tables like this one


<pre><span class=hs-linenum>89: </span><span class='hs-comment'>-- Eeks, we missed the header name!</span>
<span class=hs-linenum>90: </span>
<span class=hs-linenum>91: </span><a class=annot href="#"><span class=annottext>(CSV.CSV)</span><span class='hs-definition'>csvBad1</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:[[(GHC.Types.Char)]]
-&gt; [{VV : [[(GHC.Types.Char)]] | ((len VV) == (len x1))}]
-&gt; (CSV.CSV)</span><span class='hs-conid'>Csv</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a>  <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Date"</span></a> <span class='hs-comment'>{- ??? -}</span> <span class='hs-keyglyph'>]</span> 
<span class=hs-linenum>92: </span>              <span class=hs-error><span class='hs-keyglyph'>[</span></span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt; 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Mon"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-str'>"1"</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>93: </span>              <span class=hs-error><span class='hs-layout'>,</span></span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt; 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Tue"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-str'>"2"</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>94: </span>              <span class=hs-error><span class='hs-layout'>,</span></span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt; 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Wed"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-str'>"3"</span></a><span class='hs-keyglyph'>]</span> 
<span class=hs-linenum>95: </span>              <span class=hs-error><span class='hs-keyglyph'>]</span></span>
<span class=hs-linenum>96: </span>
</pre>

or this one, 


<pre><span class=hs-linenum>102: </span><span class='hs-comment'>-- Blergh! we missed a column.</span>
<span class=hs-linenum>103: </span>
<span class=hs-linenum>104: </span><a class=annot href="#"><span class=annottext>(CSV.CSV)</span><span class='hs-definition'>csvBad2</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:[[(GHC.Types.Char)]]
-&gt; [{VV : [[(GHC.Types.Char)]] | ((len VV) == (len x1))}]
-&gt; (CSV.CSV)</span><span class='hs-conid'>Csv</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a>  <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Name"</span></a> <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Age"</span></a>  <span class='hs-keyglyph'>]</span> 
<span class=hs-linenum>105: </span>              <span class=hs-error><span class='hs-keyglyph'>[</span></span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Alice"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"32"</span></a>   <span class='hs-keyglyph'>]</span>
<span class=hs-linenum>106: </span>              <span class=hs-error><span class='hs-layout'>,</span></span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Bob"</span></a>  <span class='hs-comment'>{- ??? -}</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>107: </span>              <span class=hs-error><span class='hs-layout'>,</span></span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Cris"</span></a> <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"29"</span></a>   <span class='hs-keyglyph'>]</span> 
<span class=hs-linenum>108: </span>              <span class=hs-error><span class='hs-keyglyph'>]</span></span>
</pre>

Alas, both the above are valid inhabitants of the Haskell `CSV` type, and 
so, sneak past GHC.

The Invariant 
-------------

Thus, we want to *refine* the `CSV` type to specify that the *number* of
elements in each row is *exactly* the same as the   *number* of headers.

To do so, we merely write a refined data type definition:


<pre><span class=hs-linenum>123: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>CSV</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Csv</span> <span class='hs-layout'>{</span> <span class='hs-varid'>headers</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>String</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>124: </span>                   <span class='hs-layout'>,</span> <span class='hs-varid'>rows</span>    <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-keyglyph'>[</span><span class='hs-conid'>String</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>|</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>v</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>len</span> <span class='hs-varid'>headers</span><span class='hs-layout'>)</span><span class='hs-layout'>}</span><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>125: </span>                   <span class='hs-layout'>}</span>
<span class=hs-linenum>126: </span>  <span class='hs-keyword'>@-}</span>
</pre>

Here `len` is a *measure* [denoting the length of a list][list-measure].
Thus, `(len headers)` is the number of headers in the table, and the
refinement on the `rows` field states that  *each* `row` is a list of `String`s, 
with exactly the same number of elements as the number of `headers`.

We can now have our arbitrary-arity tables, but LiquidHaskell will 
make sure that we don't miss entries here or there.


<pre><span class=hs-linenum>138: </span><span class='hs-comment'>-- All is well! </span>
<span class=hs-linenum>139: </span>
<span class=hs-linenum>140: </span><a class=annot href="#"><span class=annottext>(CSV.CSV)</span><span class='hs-definition'>csvGood</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:[[(GHC.Types.Char)]]
-&gt; [{VV : [[(GHC.Types.Char)]] | ((len VV) == (len x1))}]
-&gt; (CSV.CSV)</span><span class='hs-conid'>Csv</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Id"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Name"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Days"</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>141: </span>              <span class='hs-keyglyph'>[</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-str'>"1"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Jan"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"31"</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>142: </span>              <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-str'>"2"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Feb"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"28"</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>143: </span>              <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-str'>"3"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Mar"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"31"</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>144: </span>              <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-str'>"4"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Apr"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"30"</span></a><span class='hs-keyglyph'>]</span> 
<span class=hs-linenum>145: </span>              <span class='hs-keyglyph'>]</span>
</pre>

Bonus Points
------------

How would you modify the specification to prevent table with degenerate entries
like this one?


<pre><span class=hs-linenum>155: </span><a class=annot href="#"><span class=annottext>(CSV.CSV)</span><span class='hs-definition'>deg</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:[[(GHC.Types.Char)]]
-&gt; [{VV : [[(GHC.Types.Char)]] | ((len VV) == (len x1))}]
-&gt; (CSV.CSV)</span><span class='hs-conid'>Csv</span></a> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a>  <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Id"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Name"</span></a><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Days"</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>156: </span>          <span class='hs-keyglyph'>[</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-str'>"1"</span></a> <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Jan"</span></a> <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"31"</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>157: </span>          <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}]&lt;\_ VV -&gt; ((len VV) &gt;= 0)&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-keyglyph'>[</span></a><a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; false) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-str'>"2"</span></a> <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [(GHC.Types.Char)] | ((len VV) &gt;= 0)}</span><span class='hs-str'>"Feb"</span></a> <span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{VV : [{VV : (GHC.Types.Char) | false}]&lt;\_ VV -&gt; false&gt; | (((null VV)) &lt;=&gt; true) &amp;&amp; ((len VV) == 0) &amp;&amp; ((len VV) &gt;= 0)}</span><span class='hs-str'>""</span></a><span class='hs-keyglyph'>]</span>
<span class=hs-linenum>158: </span>          <span class='hs-keyglyph'>]</span>
</pre>

[shapeless-csv]: http://www.reddit.com/r/scala/comments/1nhzi2/using_shapelesss_sized_type_to_eliminate_real/
[list-measure]:  /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/ 
