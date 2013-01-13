---
layout: post
title: "Measuring Lists I"
date: 2013-01-05 16:12
author: Ranjit Jhala
published: false 
comments: true
external-url:
categories: basic
demo: lenMapReduce.hs
---

[Previously][vecbounds] we saw how liquid refinements can be pretty 
handy for enforcing invariants about integers, for example the about 
whether a `Vector` is being indexed within bounds. Now, lets see how
they can be used to encode structural invariants about data types, in
particular, lets see how to use the `measure` mechanism to talk about 
the **size** of a list, and thereby write safe versions of potentially
list manipulating functions.

<!-- more -->

Measuring the Length of a List
------------------------------

Warm Up: Safe `head` and `tail` Function
----------------------------------------

A Longer Example: MapReduce 
---------------------------



