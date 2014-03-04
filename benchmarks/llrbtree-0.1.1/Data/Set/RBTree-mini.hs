
{-@ LIQUID "--no-termination" @-}

module Foo where

data RBTree a = Leaf 
              | Node Color !BlackHeight !(RBTree a) a !(RBTree a)
              deriving (Show)

data Color = B -- ^ Black
           | R -- ^ Red
           deriving (Eq,Show)

type BlackHeight = Int

{-@ insert :: (Ord a) => a -> RBT a -> RBT a @-}
insert :: Ord a => a -> RBTree a -> RBTree a
insert kx t = turnB (insert' kx t)

{-@ turnB :: ARBT a -> RBT a @-}
turnB :: RBTree a -> RBTree a
turnB Leaf           = error "turnB"
turnB (Node _ h l x r) = Node B h l x r

{-@ insert' :: (Ord a) => a -> RBT a -> ARBT a @-}
insert' :: Ord a => a -> RBTree a -> RBTree a
insert' kx Leaf = Node R 1 Leaf kx Leaf
insert' kx s@(Node B h l x r) = case compare kx x of
    LT -> balanceL' h (insert' kx l) x r
    GT -> balanceR' h l x (insert' kx r)
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

{-@ type RBT a  = {v: (RBTree a) | (isRB v)}  @-}

{-@ type ARBT a = {v: (RBTree a) | ((isARB v) && (((col v) = B) => (isRB v)))} @-}

{-@ measure isRB           :: RBTree a -> Prop
    isRB (Leaf)            = true
    isRB (Node c h l x r)  = ((isRB l) && (isRB r) && ((c == R) => ((col l) == B) && ((col r) == B)))
  @-}

{-@ invariant {v: RBTree | (((col v) = R) || ((col v) = B))} @-}

-- isARB v => (c = R => (col l = R || col r = R))

red   = R
black = B

{-@ measure isARB          :: (RBTree a) -> Prop
    isARB (Leaf)           = false 
    isARB (Node c h l x r) = ((isRB l) && (isRB r))
  @-}

{-@ measure col :: RBTree a -> Color
    col (Node c h l x r) = c
  @-}
