
{-@ LIQUID "--no-termination" @-}

module Foo where

data RBTree a = Leaf 
              | Node Col !BlackHeight !(RBTree a) a !(RBTree a)
              deriving (Show)

type Col = Int

-- data Color = B -- ^ Black
--            | R -- ^ Red
--            deriving (Eq,Show)


type BlackHeight = Int

{-@ insert :: (Ord a) => a -> RBT a -> RBT a @-}
insert :: Ord a => a -> RBTree a -> RBTree a
insert kx t = turnB (insert' kx t)

{-@ turnB :: ARBT a -> RBT a @-}
turnB :: RBTree a -> RBTree a
turnB Leaf           = error "turnB"
turnB (Node _ h l x r) = Node 1 h l x r

{-@ insert' :: (Ord a) => a -> t:(RBT a) -> {v: ARBT a | (((col t) /= 0) => (isRB v))} @-}
insert' :: Ord a => a -> RBTree a -> RBTree a
insert' kx Leaf = Node 0 1 Leaf kx Leaf
insert' kx s@(Node 1 h l x r) = case compare kx x of
    LT -> balanceL' h (insert' kx l) x r
    GT -> balanceR' h l x (insert' kx r)
    EQ -> s
insert' kx s@(Node 0 h l x r) = case compare kx x of
    LT -> Node 0 h (insert' kx l) x r
    GT -> Node 0 h l x (insert' kx r)
    EQ -> s

{-@ balanceL' :: Int -> ARBT a -> a -> RBT a -> RBT a @-}
balanceL' :: BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceL' h (Node 0 _ (Node 0 _ a x b) y c) z d =
   Node 0 (h+1) (Node 1 h a x b) y (Node 1 h c z d)
balanceL' h (Node 0 _ a x (Node 0 _ b y c)) z d =
   Node 0 (h+1) (Node 1 h a x b) y (Node 1 h c z d)
balanceL' h l x r =  Node 1 h l x r

{-@ balanceR' :: Int -> RBT a -> a -> ARBT a -> RBT a @-}
balanceR' :: BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceR' h a x (Node 0 _ b y (Node 0 _ c z d)) =
    Node 0 (h+1) (Node 1 h a x b) y (Node 1 h c z d)
balanceR' h a x (Node 0 _ (Node 0 _ b y c) z d) =
    Node 0 (h+1) (Node 1 h a x b) y (Node 1 h c z d)
balanceR' h l x r = Node 1 h l x r

{-@ type RBT a  = {v: (RBTree a) | ((isRB v) && (isARB v))}  @-}

{-@ type ARBT a = {v: (RBTree a) | ((isARB v) && (((col v) = 1) => (isRB v)))} @-}

{-@ measure isRB           :: RBTree a -> Prop
    isRB (Leaf)            = true
    isRB (Node c h l x r)  = ((isRB l) && (isRB r) && ((c == 0) => ((col l) /= 0) && ((col r) /= 0)))
  @-}

{-@ thm              :: RBTree a -> {v:RBTree a | ((isRB v) => (isARB v)) } @-}
thm Leaf             = Leaf
thm (Node c h l x r) = Node c h (thm l) x (thm r)

{-@ invariant {v: RBTree a | ((isRB v) => (isARB v))} @-}

{-@ measure isARB          :: (RBTree a) -> Prop
    isARB (Leaf)           = false 
    isARB (Node c h l x r) = ((isRB l) && (isRB r))
  @-}

{-@ measure col :: RBTree a -> Col
    col (Node c h l x r) = c
    col (Leaf)           = 2
  @-}
