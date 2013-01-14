---
layout: post
title: "Measuring Lists II"
date: 2013-01-05 16:12
author: Ranjit Jhala
published: false 
comments: true
external-url:
categories: basic
demo: lenQuicksort.hs
---

The [last note][listlen1] we saw how to measure the length of a list
and use it to write **safe** versions of potentially unsafe operations
like `head` and `tail` and `foldr1`, all of which require non-empty lists.

Of course, having done all the work needed to reason about lengths, 
we can also specify and verify properties that *relate* the lengths
of different lists.

<!-- more -->

Basic Operations: Map, Filter, Reverse
--------------------------------------

\begin{code}
x = error "TODO"
\end{code}
Less Basic: Append, Zip, Take 
-----------------------------

A Short Example: Insertion/Quick Sort
-------------------------------------




