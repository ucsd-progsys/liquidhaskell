---
layout: post
title: "Conjoining Specifications" 
date: 2014-04-05 16:12
author: Ranjit Jhala
published: false 
comments: true
external-url:
categories: measures, abstract-refinements, red-black 
---

TODO: **Conjoining Specifications** lamport. 
TODO: composing, and, for example, 
TODO: red-black trees.

[Red Black trees][RBTwiki] trees are a classic, cold-war era, 
data structure used to efficiently represent sets, using trees
whose nodes are labeled by the set's elements, and additionally, 
are colored *red* or *black*. 

The key to efficiency is that the the trees be *balanced*. 

Of course, the easiest way to do this is to just add a *height* 
label and check that the difference of heights at each node is 
bounded (cf. [AVL trees][AVLTwiki]). But, back in the olden 
days, every bit counted -- the super cunning thing about 
Red-Black Trees is that they ensure balancedness, at the 
throwaway price of a *single bit* per node.

The catch is that the invariants are devilishly tricky.

<!-- more -->

1. **Order:** Each node's value is between those in its left and right subtrees,
2. **Color:** Each red node's children are colored black,
3. **Height:** Each root-to-leaf path has the same number of black nodes.

There are ways to encode various subsets of these using 
GADTs and such, but, like [Appel][RBTappel], I find the 
encodings rather too clever as they require a variety 
of different types and constructors to capture each 
invariant. 

One advantage of refinements is we fix the data type, 
and can then *pick and choose* which invariants we want
to verify, and *compose* them, quite trivially, via
conjunction.

Red Black Trees
---------------

Lets start with the basic type describing trees.

\begin{code}
data RBTree a = Leaf 
              | Node Color a !(RBTree a) !(RBTree a)
              deriving (Show)
\end{code}

A tree is either a `Leaf` (an empty set) or a `Node c x l r` where:

* `x` is the value at the node, 
* `l` and `r` are the left and right subtrees, and
* `c` is either `B` (black) or `R` (red). 

\begin{code}
data Color    = B -- ^ Black
              | R -- ^ Red
              deriving (Eq,Show)
\end{code}

Intuitively, the set denoted by a tree is the set of values at 
the nodes of the tree.

Over the next few posts, we will develop an implementation 
([based off this][coqRBT]) of a set library using the `RBTree` 
datatype. In particular, we will implement the API:

\begin{code} <div/>
empty  :: RBTree a
member :: a -> RBTree a -> Bool
insert :: a -> RBTree a -> RBTree a
delete :: a -> RBTree a -> RBTree a
toList :: RBTree a -> [a] 
\end{code}

and will use LiquidHaskell to *directly* and *compositionally* 
specify and enforce the various invariants.

Continue to:

* [Order][rbtOrder]
* [Color][rbtColor]
* [Height][rbtHeight]
* [Conjoin][rbtAll]

[rbtOrder]   : /blog/2014/04/07/red-black-order.lhs/ 

<!--
[rbtColor]   : /blog/2014/04/14/red-black-color.lhs/ 
[rbtHeight]  : /blog/2014/04/21/red-black-height.lhs/ 
[rbtCompose] : /blog/2014/04/28/red-black-compose.lhs/
-->
