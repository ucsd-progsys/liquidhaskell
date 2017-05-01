
{-@ LIQUID "--no-termination" @-}

module Foo where

data RBTree a = Leaf 
              | Node Color !BlackHeight !(RBTree a) a !(RBTree a)
              deriving (Show)


data Color = B -- ^ Black
           | R -- ^ Red
           deriving (Eq,Show)

type BlackHeight = Int

type RBTreeBDel a = (RBTree a, Bool)

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

-- deleteMin :: RBTree a -> RBTree a
-- deleteMin Leaf = Leaf 
-- deleteMin t = turnB' s
--   where
--     ((s, _), _) = deleteMin' t


{-@ deleteMin' :: t:RBT a -> (({v: ARBT a | ((IsB t) => (isRB v))}, Bool), a) @-}
deleteMin' :: RBTree a -> (RBTreeBDel a, a)
deleteMin' Leaf                           = error "deleteMin'"
deleteMin' (Node B _ Leaf x Leaf)         = ((Leaf, True), x)
deleteMin' (Node B _ Leaf x r@(Node R _ _ _ _)) = ((turnB r, False), x)
deleteMin' (Node R _ Leaf x r)            = ((r, False), x)
deleteMin' (Node c h l x r)               = if d then (tD, m) else (tD', m)
 where
   ((l',d),m) = deleteMin' l                -- GUESS: black l --> red l' iff d is TRUE
   tD  = unbalancedR c (h-1) l' x r
   tD' = (Node c h l' x r, False)

-- GUESS: black l --> red l' iff d is TRUE

{-@ unbalancedL :: Color -> BlackHeight -> RBT a -> a -> ARBT a -> RBTB a @-}
unbalancedL :: Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTreeBDel a
unbalancedL c h l@(Node B _ _ _ _) x r
  = (balanceL B h (turnR l) x r, c == B)
unbalancedL B h (Node R lh ll lx lr@(Node B _ _ _ _)) x r
  = (Node B lh ll lx (balanceL B h (turnR lr) x r), False)
unbalancedL _ _ _ _ _ = error "unbalancedL"


-- The left tree lacks one Black node
{-@ unbalancedR :: Color -> BlackHeight -> ARBT a -> a -> RBT a -> RBTB a @-}
unbalancedR :: Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTreeBDel a
-- Decreasing one Black node in the right
unbalancedR c h l x r@(Node B _ _ _ _)
  = (balanceR B h l x (turnR r), c == B)
-- Taking one Red node from the right and adding it to the right as Black
unbalancedR B h l x (Node R rh rl@(Node B _ _ _ _) rx rr)
  = (Node B rh (balanceR B h l x (turnR rl)) rx rr, False)
unbalancedR _ _ _ _ _ = error "unbalancedR"


{-@ balanceL :: k:Color -> BlackHeight -> {v:ARBT a | ((Red k) => (IsB v))} -> a -> {v:RBT a | ((Red k) => (IsB v))} -> RBT a @-}
balanceL B h (Node R _ (Node R _ a x b) y c) z d =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceL B h (Node R _ a x (Node R _ b y c)) z d =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceL k h l x r = Node k h l x r


{-@ balanceR :: k:Color -> BlackHeight -> {v:RBT a | ((Red k) => (IsB v))} -> a -> {v:ARBT a | ((Red k) => (IsB v))} -> RBT a @-}
balanceR :: Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceR B h a x (Node R _ b y (Node R _ c z d)) =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceR B h a x (Node R _ (Node R _ b y c) z d) =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceR k h l x r = Node k h l x r

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-@ insert :: (Ord a) => a -> RBT a -> RBT a @-}
insert :: Ord a => a -> RBTree a -> RBTree a
insert kx t = turnB (insert' kx t)

{-@ turnB :: ARBT a -> RBT a @-}
turnB Leaf           = error "turnB"
turnB (Node _ h l x r) = Node B h l x r

{-@ turnR :: RBT a -> ARBT a @-}
turnR Leaf             = error "turnR"
turnR (Node _ h l x r) = Node R h l x r

{-@ turnB' :: ARBT a -> RBT a @-}
turnB' Leaf             = Leaf
turnB' (Node _ h l x r) = Node B h l x r

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

{-@ type ARBTB a = (RBT a, Bool) @-}
{-@ type RBTB a = (RBT a, Bool)  @-}

{-@ type RBT a  = {v: (RBTree a) | (isRB v)} @-}
{- type ARBT a = {v: (RBTree a) | ((isARB v) && ((IsB v) => (isRB v)))} -}


{-@ type ARBT a = {v: (RBTree a) | (isARB v) } @-}

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

{-@ predicate Invs V = ((Inv1 V) && (Inv2 V))               @-}
{-@ predicate Inv1 V = (((isARB V) && (IsB V)) => (isRB V)) @-}
{-@ predicate Inv2 V = ((isRB v) => (isARB v))              @-}

{-@ invariant {v: RBTree a | (Invs v)} @-}

{-@ inv              :: RBTree a -> {v:RBTree a | (Invs v)} @-}
inv Leaf             = Leaf
inv (Node c h l x r) = Node c h (inv l) x (inv r)
