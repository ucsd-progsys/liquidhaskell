
{-@ LIQUID "--no-termination"   @-}

module RedBlackTree where

import Language.Haskell.Liquid.Prelude

data RBTree a = Leaf 
              | Node Color a !(RBTree a) !(RBTree a)
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

{-@ remove :: (Ord a) => a -> RBT a -> RBT a @-}
remove x t = makeBlack (del x t)

{-@ del              :: (Ord a) => a -> t:RBT a -> {v:ARBT a | ((isB t) || (isRB v))} @-}
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

{-@ append :: y:a -> l:RBT a -> r:RBT a -> (ARBT2 a l r) @-}

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

{-@ deleteMin :: RBT a -> RBT a @-}
deleteMin (Leaf)         = Leaf
deleteMin (Node _ x l r) = makeBlack t
  where 
    (_, t)               = deleteMin' x l r


{-@ deleteMin' :: k:a -> l:RBT a -> r:RBT a -> (a, ARBT2 a l r) @-}
deleteMin' k Leaf r              = (k, r)
deleteMin' x (Node R lx ll lr) r = (k, Node R x l' r)   where (k, l') = deleteMin' lx ll lr 
deleteMin' x (Node B lx ll lr) r = (k, lbalS x l' r )   where (k, l') = deleteMin' lx ll lr 

---------------------------------------------------------------------------
-- | Rotations ------------------------------------------------------------
---------------------------------------------------------------------------

{-@ lbalS                             :: k:a -> l:ARBT a -> r:RBT a -> {v: ARBT a | ((IsB r) => (isRB v))} @-}
lbalS k (Node R x a b) r              = Node R k (Node B x a b) r
lbalS k l (Node B y a b)              = let t = rbal k l (Node R y a b) in t 
lbalS k l (Node R z (Node B y a b) c) = Node R y (Node B k l a) (rbal z b (makeRed c))
lbalS k l r                           = liquidError "nein"

{-@ rbalS                             :: k:a -> l:RBT a -> r:ARBT a -> {v: ARBT a | ((IsB l) => (isRB v))} @-}
rbalS k l (Node R y b c)              = Node R k l (Node B y b c)
rbalS k (Node B x a b) r              = let t = lbal k (Node R x a b) r in t 
rbalS k (Node R x a (Node B y b c)) r = Node R y (lbal x (makeRed a) b) (Node B k c r)
rbalS k l r                           = liquidError "nein" 

{-@ lbal                              :: k:a -> l:ARBT a -> RBT a -> RBT a @-}
lbal k (Node R y (Node R x a b) c) r  = Node R y (Node B x a b) (Node B k c r)
lbal k (Node R x a (Node R y b c)) r  = Node R y (Node B x a b) (Node B k c r)
lbal k l r                            = Node B k l r

{-@ rbal                              :: k:a -> l:RBT a -> ARBT a -> RBT a  @-}
rbal x a (Node R y b (Node R z c d))  = Node R y (Node B x a b) (Node B z c d)
rbal x a (Node R z (Node R y b c) d)  = Node R y (Node B x a b) (Node B z c d)
rbal x l r                            = Node B x l r

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-@ type BlackRBT a = {v: RBT a | (IsB v)} @-}

{-@ makeRed :: l:BlackRBT a -> ARBT a @-}
makeRed (Node _ x l r) = Node R x l r
makeRed Leaf           = liquidError "nein" 

{-@ makeBlack :: ARBT a -> RBT a @-}
makeBlack Leaf           = Leaf
makeBlack (Node _ x l r) = Node B x l r

---------------------------------------------------------------------------
-- | Specifications -------------------------------------------------------
---------------------------------------------------------------------------

-- | Red-Black Trees

{-@ type RBT a    = {v: RBTree a | (isRB v)} @-}

{-@ measure isRB        :: RBTree a -> Prop
    isRB (Leaf)         = true
    isRB (Node c x l r) = ((isRB l) && (isRB r) && ((c == R) => ((IsB l) && (IsB r))))
  @-}

-- | Almost Red-Black Trees

{-@ type ARBT a    = {v: RBTree a | (isARB v) } @-}

{-@ measure isARB        :: (RBTree a) -> Prop
    isARB (Leaf)         = true 
    isARB (Node c x l r) = ((isRB l) && (isRB r))
  @-}

-- | Conditionally Red-Black Tree

{-@ type ARBT2 a L R = {v:ARBT a | (((IsB L) && (IsB R)) => (isRB v))} @-}

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

------------------------------------------------------------------
-- | Auxiliary Invariants ----------------------------------------
------------------------------------------------------------------

{-@ predicate Invs V = ((Inv1 V) && (Inv2 V))               @-}
{-@ predicate Inv1 V = (((isARB V) && (IsB V)) => (isRB V)) @-}
{-@ predicate Inv2 V = ((isRB v) => (isARB v))              @-}

{-@ invariant {v: Color | (v = R || v = B)}                 @-}

{-@ invariant {v: RBTree a | (Invs v)}                      @-}

{-@ inv            :: RBTree a -> {v:RBTree a | (Invs v)}   @-}
inv Leaf           = Leaf
inv (Node c x l r) = Node c x (inv l) (inv r)
