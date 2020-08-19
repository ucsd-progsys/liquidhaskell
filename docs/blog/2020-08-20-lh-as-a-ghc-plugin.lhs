---
layout: post
title: LiquidHaskell is a GHC Plugin
date: 2020-08-20
comments: true
author: Ranjit Jhala 
published: true
tags: basic
---

<div class="hidden">
\begin{code}
module Plugin where

incr :: Int -> Int
incr x = x + 1
\end{code}
</div>

We enjoy working with LH.

However, we would be the very first to confess that it has been incredibly
tedious to get to work on *existing* code bases, for various reasons.

1. LH ran *one file at a time*; it was a hassle to get **systematically analyze** 
   all the modules in a single package.

2. LH had *no notion of packages*; it was impossible to **import specifications** 
   across packages.

3. LH had *no integration* with the standard compilation cycle; it was difficult 
   to get robust, development-time feedback using `ghci` based tools.

We're delighted to announce the release of [LH version 0.8.10.2](TODO-LINK-TO-DOCS).

Thanks to the ingenuity and tireless efforts of our friends [Alfredo Di Napoli](TODO) 
and [Andres Loh](TODO) at [Well-Typed](http://www.well-typed.com/), this new version 
solves all three of the above problems in a single stroke, making it vastly simpler 
(dare we say, quite straightforward!) to run LH on your Haskell code.

<!-- more -->

Alfredo and Andres' key insight was that all the above problems could be solved if 
LH could be re-engineered as a **GHC Compiler Plugin** using some cool new features 
in GHC 8.10 that allows the integration of external checkers during compilation.

I strongly encourage you to check out Alfredo's talk at the [Haskell Implementor's Workshop](TODO)
if you want to learn more about the rather non-trivial mechanics of how this re-engineering
was achieved.

However, in this post, lets look at *how* and *why* to use the plugin, in particular,
how it lets us

1. Use GHC's dependency resolution to analyze entire packages with minimal recompilation;

2. Ship refined type specifications for old or new packages, and have them be verified at client code;

3. Use tools like `ghci` based IDE tooling (e.g. `ghcid` or `ghcide` to get interactive feedback),

all of which ultimately, we hope, make Liquid Haskell easier for people to use.

HEREHERE

1. Plugin Demo
--------------

* Link to plugin demo package


2. Shipping Specifications
--------------------------

* Ecosystem discussion (liquid-X packages)


3. Editor Tooling
-----------------

* Editor plugin screenshots (?)

4. Caveats
----------

- Disable?
- Liquid-Base? mirroring?

