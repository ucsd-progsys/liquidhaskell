
{-@ LIQUID "--no-termination" @-}

module Foo where

data RBTree a = Leaf 
              | Node Color !(RBTree a) a !(RBTree a)
              deriving (Show)


data Color = B -- ^ Black
           | R -- ^ Red
           deriving (Eq,Show)


type RBTreeBDel a = (RBTree a, Bool)



---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-@ deleteMin            :: RBT a -> RBT a @-}
deleteMin (Leaf)         = Leaf
deleteMin (Node _ l x r) = turnB' t
  where 
    (_, t)               = deleteMin' l x r

{-@ type ARBT2 a L R = {v:ARBT a | (((IsB L) && (IsB R)) => (isRB v))} @-}

{-@ deleteMin'                   :: l:RBT a -> a -> r:RBT a -> (a, ARBT2 a l r) @-}
deleteMin'                       :: RBTree a -> a -> RBTree a -> (a, RBTree a)
deleteMin' Leaf k r              = (k, r)
deleteMin' (Node R ll lx lr) x r = (k, Node R l' x r)   where (k, l') = deleteMin' ll lx lr 
deleteMin' (Node B ll lx lr) x r = (k, lbalS l' x r )   where (k, l') = deleteMin' ll lx lr 

{-@ lbalS                             :: ARBT a -> a -> r:RBT a -> {v: ARBT a | ((IsB r) => (isRB v))} @-}
lbalS (Node R a x b) k r              = Node R (Node B a x b) k r
lbalS l k (Node B a y b)              = let zoo = rbal' l k (Node R a y b) in zoo 
lbalS l k (Node R (Node B a y b) z c) = Node R (Node B l k a) y (rbal' b z (turnR' c))
lbalS l k r                           = Node R l k r

{-@ rbal' :: RBT a -> a -> ARBT a -> RBT a @-}
rbal' l k (Node R b y (Node R c z d)) = Node R (Node B l k b) y (Node B c z d)
rbal' l k (Node R (Node R b y c) z d) = Node R (Node B l k b) y (Node B c z d)
rbal' l k r                           = Node B l k r

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-@ turnB :: ARBT a -> RBT a @-}
turnB Leaf           = error "turnB"
turnB (Node _ l x r) = Node B l x r

{-@ turnR :: RBT a -> ARBT a @-}
turnR Leaf           = error "turnR"
turnR (Node _ l x r) = Node R l x r


{-@ turnR' :: RBT a -> ARBT a @-}
turnR' Leaf           = Leaf
turnR' (Node _ l x r) = Node R l x r


{-@ turnB' :: ARBT a -> RBT a @-}
turnB' Leaf           = Leaf
turnB' (Node _ l x r) = Node B l x r

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-@ type ARBTB a = (RBT a, Bool) @-}
{-@ type RBTB a = (RBT a, Bool)  @-}

{-@ type RBT a  = {v: (RBTree a) | (isRB v)} @-}
{- type ARBT a = {v: (RBTree a) | ((isARB v) && ((IsB v) => (isRB v)))} -}


{-@ type ARBT a = {v: (RBTree a) | (isARB v) } @-}

{-@ measure isRB        :: RBTree a -> Prop
    isRB (Leaf)         = true
    isRB (Node c l x r) = ((isRB l) && (isRB r) && ((Red c) => ((IsB l) && (IsB r))))
  @-}

{-@ measure isARB        :: (RBTree a) -> Prop
    isARB (Leaf)         = true 
    isARB (Node c l x r) = ((isRB l) && (isRB r))
  @-}

{-@ measure col         :: RBTree a -> Color
    col (Node c l x r)  = c
    col (Leaf)          = B
  @-}

{-@ predicate IsB T = not (Red (col T)) @-}
{-@ predicate Red C = C == R            @-}

-------------------------------------------------------------------------------
-- Auxiliary Invariants -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ predicate Invs V = ((Inv1 V) && (Inv2 V))               @-}
{-@ predicate Inv1 V = (((isARB V) && (IsB V)) => (isRB V)) @-}
{-@ predicate Inv2 V = ((isRB v) => (isARB v))              @-}

{-@ invariant {v: RBTree a | (Invs v)} @-}

{-@ inv              :: RBTree a -> {v:RBTree a | (Invs v)} @-}
inv Leaf           = Leaf
inv (Node c l x r) = Node c (inv l) x (inv r)
