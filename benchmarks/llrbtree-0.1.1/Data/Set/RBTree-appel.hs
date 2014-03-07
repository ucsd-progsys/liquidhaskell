
{-@ LIQUID "--no-termination" @-}

module Foo where

data RBTree a = Leaf 
              | Node Color !(RBTree a) a !(RBTree a)
              deriving (Show)

data Color = B -- ^ Black
           | R -- ^ Red
           deriving (Eq,Show)

---------------------------------------------------------------------------
-- | Add an element -------------------------------------------------------
---------------------------------------------------------------------------

{-@ add :: (Ord a) => a -> RBT a -> RBT a @-}
add x s = makeBlack (ins x s)

{-@ ins :: (Ord a) => a -> t:RBT a -> {v: ARBT a | ((IsB t) => (isRB v))} @-}

ins kx Leaf             = Node R Leaf kx Leaf
ins kx s@(Node B l x r) = case compare kx x of
                            LT -> let zoo = lbal (ins kx l) x r in zoo
                            GT -> let zoo = rbal l x (ins kx r) in zoo
                            EQ -> s
ins kx s@(Node R l x r) = case compare kx x of
                            LT -> Node R (ins kx l) x r
                            GT -> Node R l x (ins kx r)
                            EQ -> s

---------------------------------------------------------------------------
-- | Delete an element ----------------------------------------------------
---------------------------------------------------------------------------

{- del              :: (Ord a) => a -> RBT a -> ARBT a 
del x Leaf           = Leaf
del x (Node _ a y b) = case compare x y of
   EQ -> append a b 
   LT -> case a of
           Leaf         -> Node R Leaf y b
           Node B _ _ _ -> lbalS (del x a) y b
           _            -> Node R (del x a) y b
   GT -> case b of
           Leaf         -> Node R a y Leaf 
           Node B _ _ _ -> rbalS a y (del x b)
           _            -> Node R a y (del x b)

-}

{-@ append                                  :: l:RBT a -> r:RBT a -> (ARBT2 a l r) @-}
append Leaf r                               = r
append l Leaf                               = l
append (Node R ll lx lr) (Node R rl rx rr)  = case append lr rl of 
                                                Node R lr' x rl' -> Node R (Node R ll lx lr') x (Node R rl' rx rr)
                                                lrl              -> Node R ll lx (Node R lrl rx rr)
append (Node B ll lx lr) (Node B rl rx rr)  = case append lr rl of 
                                                Node R lr' x rl' -> Node R (Node B ll lx lr') x (Node B rl' rx rr)
                                                lrl              -> lbalS ll lx (Node B lrl rx rr)
append l@(Node B _ _ _) (Node R rl rx rr)   = Node R (append l rl) rx rr
append l@(Node R ll lx lr) r@(Node B _ _ _) = Node R ll lx (append lr r)

---------------------------------------------------------------------------
-- | Delete Minimum Element -----------------------------------------------
---------------------------------------------------------------------------

{-@ deleteMin            :: RBT a -> RBT a @-}
deleteMin (Leaf)         = Leaf
deleteMin (Node _ l x r) = makeBlack t
  where 
    (_, t)               = deleteMin' l x r


{-@ deleteMin'                   :: l:RBT a -> a -> r:RBT a -> (a, ARBT2 a l r) @-}
deleteMin'                       :: RBTree a -> a -> RBTree a -> (a, RBTree a)
deleteMin' Leaf k r              = (k, r)
deleteMin' (Node R ll lx lr) x r = (k, Node R l' x r)   where (k, l') = deleteMin' ll lx lr 
deleteMin' (Node B ll lx lr) x r = (k, lbalS l' x r )   where (k, l') = deleteMin' ll lx lr 

---------------------------------------------------------------------------
-- | Rotations ------------------------------------------------------------
---------------------------------------------------------------------------

{-@ lbalS                             :: ARBT a -> a -> r:RBT a -> {v: ARBT a | ((IsB r) => (isRB v))} @-}
lbalS (Node R a x b) k r              = Node R (Node B a x b) k r
lbalS l k (Node B a y b)              = let zoo = rbal l k (Node R a y b) in zoo 
lbalS l k (Node R (Node B a y b) z c) = Node R (Node B l k a) y (rbal b z (makeRed c))
lbalS l k r                           = Node R l k r

{-@ rbalS                             :: l:RBT a -> a -> ARBT a -> {v: ARBT a | ((IsB l) => (isRB v))} @-}
rbalS l k (Node R b y c)              = Node R l k (Node B b y c)
rbalS (Node B a x b) k r              = let zoo = lbal (Node R a x b) k r in zoo
rbalS (Node R a x (Node B b y c)) k r = Node R (lbal (makeRed a) x b) y (Node B c k r)
rbalS l k r                           = Node R l k r

{-@ lbal                              :: ARBT a -> a -> RBT a -> RBT a @-}
lbal (Node R (Node R a x b) y c) k r  = Node R (Node B a x b) y (Node B c k r)
lbal (Node R a x (Node R b y c)) k r  = Node R (Node B a x b) y (Node B c k r)
lbal l k r                            = Node B l k r

{-@ rbal                              :: RBT a -> a -> ARBT a -> RBT a @-}
rbal a x (Node R b y (Node R c z d))  = Node R (Node B a x b) y (Node B c z d)
rbal a x (Node R (Node R b y c) z d)  = Node R (Node B a x b) y (Node B c z d)
rbal l x r                            = Node B l x r

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-@ makeRed :: RBT a -> ARBT a @-}
makeRed Leaf           = Leaf
makeRed (Node _ l x r) = Node R l x r

{-@ makeBlack :: ARBT a -> RBT a @-}
makeBlack Leaf           = Leaf
makeBlack (Node _ l x r) = Node B l x r

-- DEAD -- {- turnB :: ARBT a -> RBT a -}
-- DEAD -- turnB Leaf           = error "turnB"
-- DEAD -- turnB (Node _ l x r) = Node B l x r
-- DEAD -- 
-- DEAD -- {- turnR :: RBT a -> ARBT a -}
-- DEAD -- turnR Leaf           = error "turnR"
-- DEAD -- turnR (Node _ l x r) = Node R l x r
-- DEAD -- {- rbal' :: RBT a -> a -> ARBT a -> RBT a -}
-- DEAD -- rbal' l k (Node R b y (Node R c z d)) = Node R (Node B l k b) y (Node B c z d)
-- DEAD -- rbal' l k (Node R (Node R b y c) z d) = Node R (Node B l k b) y (Node B c z d)
-- DEAD -- rbal' l k r                           = Node B l k r


---------------------------------------------------------------------------
-- | Specifications -------------------------------------------------------
---------------------------------------------------------------------------

-- | Red-Black Trees

{-@ type RBT a  = {v: (RBTree a) | (isRB v)} @-}

{-@ measure isRB        :: RBTree a -> Prop
    isRB (Leaf)         = true
    isRB (Node c l x r) = ((isRB l) && (isRB r) && ((Red c) => ((IsB l) && (IsB r))))
  @-}

-- | Almost Red-Black Trees

{-@ type ARBT a = {v: (RBTree a) | (isARB v) } @-}

{-@ measure isARB        :: (RBTree a) -> Prop
    isARB (Leaf)         = true 
    isARB (Node c l x r) = ((isRB l) && (isRB r))
  @-}

-- | Conditionally Red-Black Tree

{-@ type ARBT2 a L R = {v:ARBT a | (((IsB L) && (IsB R)) => (isRB v))} @-}

-- | Color of a tree

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
