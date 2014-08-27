---
layout: post
title: "Red-Black Trees: Order"
date: 2014-04-05 16:12
author: Ranjit Jhala
published: false 
comments: true
external-url:
categories: measures, abstract-refinements 
demo: RBTree-ord.hs
---

A data structure that implements a *set* interface, must 
provide an efficient way to determine *membership*, i.e. 
a function 

\begin{code}
member :: a -> RBTree a -> Bool
\end{code}

where `elem x xs` returns `True` iff `x` is in the set denoted by `xs`.

Red Black trees are use 

To enable effici

Abstract Refinements vs. Indices
--------------------------------

Most formal accounts of Red Black trees eschew the order 
invariant as it is rather cumbersome to encode using GADTs
and indexed-types -- one must index the structure with lower
and upper bounds, and appropriately adjust these bounds at 
rotations. 


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

Continue to:

* [Order][rbtOrder]
* [Color][rbtColor]
* [Height][rbtHeight]
* [Composition][rbtAll]

[rbtOrder]   : /blog/2014/04/07/red-black-order.lhs/ 
[rbtColor]   : /blog/2014/04/14/red-black-color.lhs/ 
[rbtHeight]  : /blog/2014/04/21/red-black-height.lhs/ 
[rbtCompose] : /blog/2014/04/28/red-black-compose.lhs/


Red-Black Trees
---------------

Abstract Refinements
--------------------

Ordered Trees
-------------


Over the next several posts, lets see how to develop an
RBTree library, using LiquidHaskell to directly and 
compositionally specify and enforce the above invariants.



<div class="hidden">

\begin{code}
{-@ LIQUID "--no-termination"   @-}
module Foo (add, remove, deleteMin, deleteMin') where
import Language.Haskell.Liquid.Prelude
\end{code}

</div>

ADD

\begin{code}
data Color    = B -- ^ Black
              | R -- ^ Red
              deriving (Eq,Show)
\end{code}

\begin{code}
data RBTree a = Leaf 
              | Node Color a !(RBTree a) !(RBTree a)
              deriving (Show)
\end{code}

---------------------------------------------------------------------------
-- | Add an element -------------------------------------------------------
---------------------------------------------------------------------------

{-@ add :: (Ord a) => a -> ORBT a -> ORBT a @-}
add x s = makeBlack (ins x s)

{-@ ins :: (Ord a) => a -> ORBT a -> ORBT a @-}
ins kx Leaf             = Node R kx Leaf Leaf
ins kx s@(Node B x l r) = case compare kx x of
                            LT -> let t = lbal x (ins kx l) r in t 
                            GT -> let t = rbal x l (ins kx r) in t 
                            EQ -> s
ins kx s@(Node R x l r) = case compare kx x of
                            LT -> Node R x (ins kx l) r
                            GT -> Node R x l (ins kx r)
                            EQ -> s

---------------------------------------------------------------------------
-- | Delete an element ----------------------------------------------------
---------------------------------------------------------------------------

{-@ remove :: (Ord a) => a -> ORBT a -> ORBT a @-}
remove x t = makeBlack (del x t)

{-@ del              :: (Ord a) => a -> ORBT a -> ORBT a @-}
del x Leaf           = Leaf
del x (Node _ y a b) = case compare x y of
   EQ -> append y a b 
   LT -> case a of
           Leaf         -> Node R y Leaf b
           Node B _ _ _ -> lbalS y (del x a) b
           _            -> let t = Node R y (del x a) b in t 
   GT -> case b of
           Leaf         -> Node R y a Leaf 
           Node B _ _ _ -> rbalS y a (del x b)
           _            -> Node R y a (del x b)

{-@ append  :: y:a -> ORBT {v:a | v < y} -> ORBT {v:a | y < v} -> ORBT a @-}
append :: a -> RBTree a -> RBTree a -> RBTree a

append _ Leaf r                               
  = r

append _ l Leaf                               
  = l

append piv (Node R lx ll lr) (Node R rx rl rr)  
  = case append piv lr rl of 
      Node R x lr' rl' -> Node R x (Node R lx ll lr') (Node R rx rl' rr)
      lrl              -> Node R lx ll (Node R rx lrl rr)

append piv (Node B lx ll lr) (Node B rx rl rr)  
  = case append piv lr rl of 
      Node R x lr' rl' -> Node R x (Node B lx ll lr') (Node B rx rl' rr)
      lrl              -> lbalS lx ll (Node B rx lrl rr)

append piv l@(Node B _ _ _) (Node R rx rl rr)   
  = Node R rx (append piv l rl) rr

append piv l@(Node R lx ll lr) r@(Node B _ _ _) 
  = Node R lx ll (append piv lr r)

---------------------------------------------------------------------------
-- | Delete Minimum Element -----------------------------------------------
---------------------------------------------------------------------------

{-@ deleteMin  :: ORBT a -> ORBT a @-}
deleteMin (Leaf)         = Leaf
deleteMin (Node _ x l r) = makeBlack t
  where 
    (_, t)               = deleteMin' x l r


{-@ deleteMin' :: k:a -> ORBT {v:a | v < k} -> ORBT {v:a | k < v} -> (a, ORBT a) @-}
deleteMin' k Leaf r              = (k, r)
deleteMin' x (Node R lx ll lr) r = (k, Node R x l' r)   where (k, l') = deleteMin' lx ll lr 
deleteMin' x (Node B lx ll lr) r = (k, lbalS x l' r )   where (k, l') = deleteMin' lx ll lr 

---------------------------------------------------------------------------
-- | Rotations ------------------------------------------------------------
---------------------------------------------------------------------------

lbalS k (Node R x a b) r              = Node R k (Node B x a b) r
lbalS k l (Node B y a b)              = let t = rbal k l (Node R y a b) in t 
lbalS k l (Node R z (Node B y a b) c) = Node R y (Node B k l a) (rbal z b (makeRed c))
lbalS k l r                           = error "nein" 

rbalS k l (Node R y b c)              = Node R k l (Node B y b c)
rbalS k (Node B x a b) r              = let t = lbal k (Node R x a b) r in t 
rbalS k (Node R x a (Node B y b c)) r = Node R y (lbal x (makeRed a) b) (Node B k c r)
rbalS k l r                           = error "nein"

lbal k (Node R y (Node R x a b) c) r  = Node R y (Node B x a b) (Node B k c r)
lbal k (Node R x a (Node R y b c)) r  = Node R y (Node B x a b) (Node B k c r)
lbal k l r                            = Node B k l r

rbal x a (Node R y b (Node R z c d))  = Node R y (Node B x a b) (Node B z c d)
rbal x a (Node R z (Node R y b c) d)  = Node R y (Node B x a b) (Node B z c d)
rbal x l r                            = Node B x l r

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

makeRed (Node _ x l r)   = Node R x l r
makeRed Leaf             = error "nein" 

makeBlack Leaf           = Leaf
makeBlack (Node _ x l r) = Node B x l r

---------------------------------------------------------------------------
-- | Specifications -------------------------------------------------------
---------------------------------------------------------------------------

-- | Ordered Red-Black Trees

{-@ type ORBT a = RBTree <{\root v -> v < root }, {\root v -> v > root}> a @-}

-- | Binary Search Ordering

{-@ data RBTree a <l :: a -> a -> Prop, r :: a -> a -> Prop>
            = Leaf
            | Node (c    :: Color)
                   (key  :: a)
                   (left :: RBTree <l, r> (a <l key>))
                   (left :: RBTree <l, r> (a <r key>))
  @-}
