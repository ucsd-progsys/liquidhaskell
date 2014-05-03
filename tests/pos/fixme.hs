
{-@ LIQUID "--no-termination"   @-}

module Foo where

import Language.Haskell.Liquid.Prelude

data RBTree a = Leaf 
              | Node Color a !(RBTree a) !(RBTree a)
--               deriving (Show)

data Color = B -- ^ Black
           | R -- ^ Red
--           deriving (Eq,Show)


{-@ deleteMin'                   :: k:a -> l:RBT {v:a | v < k} -> r:RBTN {v:a | k < v} {(bh l)} -> (a, ARBT2 a l r) @-}

-- with the sig it is SAFE 

-- deleteMin' :: a -> RBTree a -> RBTree a -> (a, RBTree a)
deleteMin' k Leaf r              = (k, r)
deleteMin' x (Node R lx ll lr) r = (k, Node R x l' r)   where (k, l') = deleteMin' lx ll lr 


-- | Ordered Red-Black Trees

{-@ type ORBT a = RBTree <{\root v -> v < root }, {\root v -> v > root}> a @-}

-- | Red-Black Trees

{-@ type RBT a    = {v: (ORBT a) | ((isRB v) && (isBH v)) } @-}
{-@ type RBTN a N = {v: (RBT a) | (bh v) = N }              @-}

{-@ type ORBTL a X = RBT {v:a | v < X} @-}
{-@ type ORBTG a X = RBT {v:a | X < v} @-}

{-@ measure isRB        :: RBTree a -> Prop
    isRB (Leaf)         = true
    isRB (Node c x l r) = ((isRB l) && (isRB r) && ((c == R) => ((IsB l) && (IsB r))))
  @-}

-- | Almost Red-Black Trees

{-@ type ARBT a    = {v: (ORBT a) | ((isARB v) && (isBH v))} @-}
{-@ type ARBTN a N = {v: (ARBT a)   | (bh v) = N }             @-}

{-@ measure isARB        :: (RBTree a) -> Prop
    isARB (Leaf)         = true 
    isARB (Node c x l r) = ((isRB l) && (isRB r))
  @-}

-- | Conditionally Red-Black Tree

{-@ type ARBT2 a L R = {v:ARBTN a {(bh L)} | (((IsB L) && (IsB R)) => (isRB v))} @-}

-- | Color of a tree

{-@ measure col         :: RBTree a -> Color
    col (Node c x l r)  = c
    col (Leaf)          = B
  @-}

{-@ measure isB        :: RBTree a -> Prop
    isB (Leaf)         = false
    isB (Node c x l r) = c == B 
  @-}

{-@ predicate IsB T = not ((col T) == R) @-}

-- | Black Height

{-@ measure isBH        :: RBTree a -> Prop
    isBH (Leaf)         = true
    isBH (Node c x l r) = ((isBH l) && (isBH r) && (bh l) = (bh r))
  @-}

{-@ measure bh        :: RBTree a -> Int
    bh (Leaf)         = 0
    bh (Node c x l r) = (bh l) + (if (c == R) then 0 else 1) 
  @-}

-- | Binary Search Ordering

{-@ data RBTree a <l :: a -> a -> Prop, r :: a -> a -> Prop>
            = Leaf
            | Node (c    :: Color)
                   (key  :: a)
                   (left :: RBTree <l, r> (a <l key>))
                   (left :: RBTree <l, r> (a <r key>))
  @-}

-------------------------------------------------------------------------------
-- Auxiliary Invariants -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ predicate Invs V = ((Inv1 V) && (Inv2 V) && (Inv3 V))   @-}
{-@ predicate Inv1 V = (((isARB V) && (IsB V)) => (isRB V)) @-}
{-@ predicate Inv2 V = ((isRB v) => (isARB v))              @-}
{-@ predicate Inv3 V = 0 <= (bh v)                          @-}

{-@ invariant {v: Color | (v = R || v = B)}                 @-}

{-@ invariant {v: RBTree a | (Invs v)}                      @-}
