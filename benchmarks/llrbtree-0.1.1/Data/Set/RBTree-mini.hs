
{-@ LIQUID "--no-termination" @-}

module Data.Set.RBTree where


-- insert'   :: a -> t:OK -> {   root t = Black => v:OK tree (but maybe RED ROOT)
--                            /\ root t = RED => v:returns OK/ALMOST-OK tree (maybe R-R)
                             }

-- balanceL' :: l:ALMOST-OK -> r:OK -> OK 
-- balanceR' :: l:OK -> r:ALMOST-OK -> OK

data RBTree a = Leaf -- color is Black
              | Node Color !BlackHeight !(RBTree a) a !(RBTree a)
              deriving (Show)

data Color = B -- ^ Black
           | R -- ^ Red
           deriving (Eq,Show)

type BlackHeight = Int

insert :: Ord a => a -> RBTree a -> RBTree a
insert kx t = turnB (insert' kx t)

turnB :: RBTree a -> RBTree a
turnB Leaf           = error "turnB"
turnB (Node _ h l x r) = Node B h l x r

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

{-@ balanceL' :: Int -> 
balanceL' :: BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceL' h (Node R _ (Node R _ a x b) y c) z d =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceL' h (Node R _ a x (Node R _ b y c)) z d =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceL' h l x r = Node B h l x r

balanceR' :: BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceR' h a x (Node R _ b y (Node R _ c z d)) =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceR' h a x (Node R _ (Node R _ b y c) z d) =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceR' h l x r = Node B h l x r

{-@ type RBT a = {v: RBTr
{-@ measure isRB           :: RBTree a -> Prop
    isRB Leaf              = true
    isRB (Node c h l x r)  = (isRB l) && (isRB r) && ((c == B) => ((color l) == B) && ((color r) == B))
  @-}


{-@ measure isARB          :: RBTree a -> Prop
    isARB Leaf             = false 
    isARB (Node c h l x r) = (isRB l) && (isRB r)
  @-}
