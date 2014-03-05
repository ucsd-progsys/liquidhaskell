
{-@ LIQUID "--no-termination" @-}

module Foo where

data RBTree a = Leaf 
              | Node Color !BlackHeight !(RBTree a) a !(RBTree a)
              deriving (Show)


data Color = B -- ^ Black
           | R -- ^ Red
           deriving (Eq,Show)

type BlackHeight = Int

{-@ invariant {v:Color | (v = B || v = R) } @-}

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------


-- delete :: Ord a => a -> RBTree a -> RBTree a
-- delete x t = turnB' s
--   where
--     (s,_) = delete' x t
-- 
-- delete' :: Ord a => a -> RBTree a -> RBTreeBDel a
-- delete' _ Leaf = (Leaf, False)
-- delete' x (Node c h l y r) = case compare x y of
--     LT -> let (l',d) = delete' x l
--               t = Node c h l' y r
--           in if d then unbalancedR c (h-1) l' y r else (t, False)
--     GT -> let (r',d) = delete' x r
--               t = Node c h l y r'
--           in if d then unbalancedL c (h-1) l y r' else (t, False)
--     EQ -> case r of
--         Leaf -> if c == B then blackify l else (l, False)
--         _ -> let ((r',d),m) = deleteMin' r
--                  t = Node c h l m r'
--              in if d then unbalancedL c (h-1) l m r' else (t, False)


---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-@ insert :: (Ord a) => a -> RBT a -> RBT a @-}
insert :: Ord a => a -> RBTree a -> RBTree a
insert kx t = turnB (insert' kx t)

{-@ turnB :: ARBT a -> RBT a @-}
turnB :: RBTree a -> RBTree a
turnB Leaf           = error "turnB"
turnB (Node _ h l x r) = Node B h l x r

{-@ insert' :: (Ord a) => a -> t:RBT a -> {v: ARBT a | ((IsB t) => (isRB v))} @-}
insert' :: Ord a => a -> RBTree a -> RBTree a
insert' kx Leaf = Node R 1 Leaf kx Leaf
insert' kx s@(Node B h l x r) = case compare kx x of
    LT -> let zoo = balanceL' h (insert' kx l) x r in zoo
    GT -> let zoo = balanceR' h l x (insert' kx r) in zoo
    EQ -> s
insert' kx s@(Node R h l x r) = case compare kx x of
    LT -> Node R h (insert' kx l) x r
    GT -> Node R h l x (insert' kx r)
    EQ -> s

{-@ balanceL' :: Int -> ARBT a -> a -> RBT a -> RBT a @-}
balanceL' :: BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceL' h (Node R _ (Node R _ a x b) y c) z d =
   Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceL' h (Node R _ a x (Node R _ b y c)) z d =
   Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceL' h l x r =  Node B h l x r

{-@ balanceR' :: Int -> RBT a -> a -> ARBT a -> RBT a @-}
balanceR' :: BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceR' h a x (Node R _ b y (Node R _ c z d)) =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceR' h a x (Node R _ (Node R _ b y c) z d) =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceR' h l x r = Node B h l x r

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-@ type RBT a  = {v: (RBTree a) | (isRB v)}  @-}

{-@ type ARBT a = {v: (RBTree a) | (isARB v)} @-}

{-@ measure isRB           :: RBTree a -> Prop
    isRB (Leaf)            = true
    isRB (Node c h l x r)  = ((isRB l) && (isRB r) && ((Red c) => ((IsB l) && (IsB r))))
  @-}

{-@ measure isARB          :: (RBTree a) -> Prop
    isARB (Leaf)           = true 
    isARB (Node c h l x r) = ((isRB l) && (isRB r))
  @-}

{-@ measure col :: RBTree a -> Color
    col (Node c h l x r) = c
    col (Leaf)           = B
  @-}

{-@ predicate IsB T = not (Red (col T)) @-}
{-@ predicate Red C = C == R            @-}

-------------------------------------------------------------------------------
-- Auxiliary Invariants -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ invariant {v: RBTree a | ((isRB v) => (isARB v))} @-}

{-@ inv              :: RBTree a -> {v:RBTree a | ((isRB v) => (isARB v)) } @-}
inv Leaf             = Leaf
inv (Node c h l x r) = Node c h (inv l) x (inv r)


