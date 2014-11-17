

Multiple Measures: Red-Black Trees
==================================


<div class="hidden">

\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diff"           @-}

module RBTree (ok, bad1, bad2) where

import Language.Haskell.Liquid.Prelude

ok, bad1, bad2 :: RBTree Int

---------------------------------------------------------------------------
-- | Specifications -------------------------------------------------------
---------------------------------------------------------------------------

-- | Ordered Red-Black Trees

{-@ type ORBT a = RBTree <{\root v -> v < root }, {\root v -> v > root}> a @-}

-- | Red-Black Trees
{-@ type RBT a    = {v: ORBT a | isRB v && isBH v } @-}

{-@ measure isRB        :: RBTree a -> Prop
    isRB (Leaf)         = true
    isRB (Node c x l r) = isRB l && isRB r && (c == R => (IsB l && IsB r))
  @-}

-- | Almost Red-Black Trees
{-@ type ARBT a    = {v: ORBT a | isARB v && isBH v} @-}

{-@ measure isARB        :: (RBTree a) -> Prop
    isARB (Leaf)         = true 
    isARB (Node c x l r) = (isRB l && isRB r)
  @-}

-- | Color of a tree
{-@ measure col         :: RBTree a -> Color
    col (Node c x l r)  = c
    col (Leaf)          = B
  @-}

{-@ measure isB        :: RBTree a -> Prop
    isB (Leaf)         = false
    isB (Node c x l r) = c == B 
  @-}

{-@ predicate IsB T = not (col T == R) @-}

-- | Black Height
{-@ measure isBH        :: RBTree a -> Prop
    isBH (Leaf)         = true
    isBH (Node c x l r) = (isBH l && isBH r && bh l = bh r)
  @-}

{-@ measure bh        :: RBTree a -> Int
    bh (Leaf)         = 0
    bh (Node c x l r) = bh l + if (c == R) then 0 else 1 
  @-}

-- | Binary Search Ordering
{-@ data RBTree a <l :: a -> a -> Prop, r :: a -> a -> Prop>
            = Leaf
            | Node (c     :: Color)
                   (key   :: a)
                   (left  :: RBTree <l, r> (a <l key>))
                   (right :: RBTree <l, r> (a <r key>))
  @-}

-------------------------------------------------------------------------------
-- Auxiliary Invariants -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ predicate Invs V = Inv1 V && Inv2 V && Inv3 V   @-}
{-@ predicate Inv1 V = (isARB V && IsB V) => isRB V @-}
{-@ predicate Inv2 V = isRB v => isARB v            @-}
{-@ predicate Inv3 V = 0 <= bh v                    @-}
{-@ invariant {v: Color | v = R || v = B}           @-}
{-@ invariant {v: RBTree a | Invs v}                @-}

{-@ inv :: RBTree a -> {v:RBTree a | Invs v}        @-}
inv Leaf           = Leaf
inv (Node c x l r) = Node c x (inv l) (inv r)

{-@ invc :: t:RBTree a -> {v:RBTree a | Invs t }  @-}
invc Leaf           =  Leaf
invc (Node c x l r) =  Node c x  (invc l) (invc r)
  
\end{code}

</div>



 {#asdad}
---------

<img src="../img/RedBlack.png" height=300px>
+ <div class="fragment">**Color Invariant:** `Red` nodes have `Black` children</div>
+ <div class="fragment">**Height Invariant:** Number of `Black` nodes equal on *all paths*</div>
+ <div class="fragment">**Order Invariant:** Left keys < root < Right keys </div>
<br>

Basic Type 
----------

\begin{code}
data Color = R | B

data RBTree a
  = Leaf
  | Node { c     :: Color
         , key   :: a
         , left  :: RBTree a 
         , right :: RBTree a }
\end{code}


1. Color Invariant 
------------------

`Red` nodes have `Black` children

<div class="fragment">
\begin{spec}
measure isRB        :: Tree a -> Prop
isRB (Leaf)         = true
isRB (Node c x l r) = c = R => (isB l && isB r)
                      && isRB l && isRB r
\end{spec}
</div>

<div class="fragment">
where 
\begin{spec}
measure isB         :: Tree a -> Prop 
isB (Leaf)          = true
isB (Node c x l r)  = c == B
\end{spec}
</div>

1. *Almost* Color Invariant 
---------------------------

<br>

Color Invariant **except** at root. 

<br>

<div class="fragment">
\begin{spec}
measure isAlmost        :: RBTree a -> Prop
isAlmost (Leaf)         = true
isAlmost (Node c x l r) = isRB l && isRB r
\end{spec}
</div>


2. Height Invariant
-------------------

Number of `Black` nodes equal on **all paths**

<div class="fragment">
\begin{spec} 
measure isBH        :: RBTree a -> Prop
isBH (Leaf)         =  true
isBH (Node c x l r) =  bh l = bh r 
                    && isBH l && isBH r 
\end{spec}
</div>

<div class="fragment">

where

\begin{spec}
measure bh        :: RBTree a -> Int
bh (Leaf)         = 0
bh (Node c x l r) = bh l 
                  + if c = Red then 0 else 1
\end{spec}
</div>

3. Order Invariant
------------------

<br>

**Binary Search Ordering**

\begin{spec}
data RBTree a
  = Leaf
  | Node { c     :: Color
         , key   :: a
         , left  :: RBTree {v:a | v < key}
         , right :: RBTree {v:a | key < v}
         }
\end{spec}


Valid Red-Black Trees
---------------------

\begin{spec}
-- Red-Black Trees
type RBT a  = {v:RBTree a | isRB v && isBH v}

-- Almost Red-Black Trees
type ARBT a = {v:RBTree a | isAlmost v && isBH v}
\end{spec}

<br>

[Details](https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/pos/RBTree.hs)

Example: OK Tree
----------------

**Satisfies All Invariants**

<img src="../img/rbtree-ok.png" height=200px>

<br>

\begin{code}
{-@ ok :: RBT Int @-}
ok = Node R 2 
          (Node B 1 Leaf Leaf)
          (Node B 3 Leaf Leaf)
\end{code}


Example: Bad Tree
-----------------

**Violates Order Invariant**

<img src="../img/rbtree-bad1.png" height=200px>

<br>

\begin{code}
{-@ bad1 :: RBT Int @-}
bad1 = Node R 1
          (Node B 2 Leaf Leaf)
          (Node B 3 Leaf Leaf)
\end{code}

Example: Bad Tree
-----------------

**Violates Color Invariant**

<img src="../img/rbtree-bad2.png" height=200px>

<br>

\begin{code}
{-@ bad2 :: RBT Int @-}
bad2 = Node R 2
         (Node R 1 Leaf Leaf)
         (Node B 3 Leaf Leaf)
\end{code}


Verified Red-Black Trees
------------------------

\begin{spec}
type RBT a  = {v:RBTree a | isRB v && isBH v}
\end{spec}

**Type System Verifies Correctness of**

<br>

+ Insertion

+ Deletion

+ Lookup

+ ... 
<br>

**In presence of rotation/rebalancing etc.**

<br>

[Details](https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/pos/RBTree.hs)

