
{-@ LIQUID "--no-termination"   @-}

module Foo where

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

{-@ ins :: (Ord a) => a -> t:RBT a -> {v: ARBTN a {(bh t)} | ((IsB t) => (isRB v))} @-}
ins kx Leaf             = Node R kx Leaf Leaf
ins kx s@(Node B x l r) = case compare kx x of
                            LT -> let zoo = lbal (ins kx l) x r in zoo
                            GT -> let zoo = rbal l x (ins kx r) in zoo
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

{-@ predicate HDel T V = (bh V) = (if (isB T) then (bh T) - 1 else (bh T)) @-}

{-@ del              :: (Ord a) => a -> t:RBT a -> {v:ARBT a | ((HDel t v) && ((isB t) || (isRB v)))} @-}
del x Leaf           = Leaf
del x (Node _ y a b) = case compare x y of
   EQ -> append a b 
   LT -> case a of
           Leaf         -> Node R y Leaf b
           Node B _ _ _ -> lbalS (del x a) y b
           _            -> let zoo = Node R y (del x a) b in zoo 
   GT -> case b of
           Leaf         -> Node R y a Leaf 
           Node B _ _ _ -> rbalS a y (del x b)
           _            -> Node R y a (del x b)

{-@ append                                  :: l:RBT a -> r:RBTN a {(bh l)} -> (ARBT2 a l r) @-}
append Leaf r                               = r
append l Leaf                               = l
append (Node R lx ll lr) (Node R rx rl rr)  = case append lr rl of 
                                                Node R x lr' rl' -> Node R x (Node R lx ll lr') (Node R rx rl' rr)
                                                lrl              -> Node R lx ll (Node R rx lrl rr)
append (Node B lx ll lr) (Node B rx rl rr)  = case append lr rl of 
                                                Node R x lr' rl' -> Node R x (Node B lx ll lr') (Node B rx rl' rr)
                                                lrl              -> lbalS ll lx (Node B rx lrl rr)
append l@(Node B _ _ _) (Node R rx rl rr)   = Node R rx (append l rl) rr
append l@(Node R lx ll lr) r@(Node B _ _ _) = Node R lx ll (append lr r)

---------------------------------------------------------------------------
-- | Delete Minimum Element -----------------------------------------------
---------------------------------------------------------------------------

{-@ deleteMin            :: RBT a -> RBT a @-}
deleteMin (Leaf)         = Leaf
deleteMin (Node _ x l r) = makeBlack t
  where 
    (_, t)               = deleteMin' l x r


{-@ deleteMin'                   :: l:RBT a -> a -> r:RBTN a {(bh l)} -> (a, ARBT2 a l r) @-}
deleteMin' Leaf k r              = (k, r)
deleteMin' (Node R lx ll lr) x r = (k, Node R x l' r)   where (k, l') = deleteMin' ll lx lr 
deleteMin' (Node B lx ll lr) x r = (k, lbalS l' x r )   where (k, l') = deleteMin' ll lx lr 

---------------------------------------------------------------------------
-- | Rotations ------------------------------------------------------------
---------------------------------------------------------------------------

{-@ lbalS                             :: l:ARBT a -> a -> r:RBTN a {1 + (bh l)} -> {v: ARBTN a {1 + (bh l)} | ((IsB r) => (isRB v))} @-}
lbalS (Node R x a b) k r              = Node R k (Node B x a b) r
lbalS l k (Node B y a b)              = let zoo = rbal l k (Node R y a b) in zoo 
lbalS l k (Node R z (Node B y a b) c) = Node R y (Node B k l a) (rbal b z (makeRed c))
lbalS l k r                           = liquidError "nein" -- Node R l k r

{-@ rbalS                             :: l:RBT a -> a -> r:ARBTN a {(bh l) - 1} -> {v: ARBTN a {(bh l)} | ((IsB l) => (isRB v))} @-}
rbalS l k (Node R y b c)              = Node R k l (Node B y b c)
rbalS (Node B x a b) k r              = let zoo = lbal (Node R x a b) k r in zoo
rbalS (Node R x a (Node B y b c)) k r = Node R y (lbal (makeRed a) x b) (Node B k c r)
rbalS l k r                           = liquidError "nein" -- Node R l k r

{-@ lbal                              :: l:ARBT a -> a -> RBTN a {(bh l)} -> RBTN a {1 + (bh l)} @-}
lbal (Node R y (Node R x a b) c) k r  = Node R y (Node B x a b) (Node B k c r)
lbal (Node R x a (Node R y b c)) k r  = Node R y (Node B x a b) (Node B k c r)
lbal l k r                            = Node B k l r

{-@ rbal                              :: l:RBT a -> a -> ARBTN a {(bh l)} -> RBTN a {1 + (bh l)} @-}
rbal a x (Node R y b (Node R z c d))  = Node R y (Node B x a b) (Node B z c d)
rbal a x (Node R z (Node R y b c) d)  = Node R y (Node B x a b) (Node B z c d)
rbal l x r                            = Node B x l r

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-@ type BlackRBT a = {v: RBT a | ((IsB v) && (bh v) > 0)} @-}

{-@ makeRed :: l:BlackRBT a -> ARBTN a {(bh l) - 1} @-}
makeRed (Node _ x l r) = Node R x l r
makeRed Leaf           = liquidError "nein" 

{-@ makeBlack :: ARBT a -> RBT a @-}
makeBlack Leaf           = Leaf
makeBlack (Node _ x l r) = Node B x l r

---------------------------------------------------------------------------
-- | Specifications -------------------------------------------------------
---------------------------------------------------------------------------

-- | Red-Black Trees

{-@ type RBT a    = {v: (RBTree a) | ((isRB v) && (isBH v)) } @-}
{-@ type RBTN a N = {v: (RBT a) | (bh v) = N }                @-}

{-@ measure isRB        :: RBTree a -> Prop
    isRB (Leaf)         = true
    isRB (Node c x l r) = ((isRB l) && (isRB r) && ((c == R) => ((IsB l) && (IsB r))))
  @-}

-- | Almost Red-Black Trees

{-@ type ARBT a    = {v: (RBTree a) | ((isARB v) && (isBH v))} @-}
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

-------------------------------------------------------------------------------
-- Auxiliary Invariants -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ predicate Invs V = ((Inv1 V) && (Inv2 V) && (Inv3 V))   @-}
{-@ predicate Inv1 V = (((isARB V) && (IsB V)) => (isRB V)) @-}
{-@ predicate Inv2 V = ((isRB v) => (isARB v))              @-}
{-@ predicate Inv3 V = 0 <= (bh v)                          @-}

{-@ invariant {v: Color | (v = R || v = B)}                 @-}

{-@ invariant {v: RBTree a | (Invs v)}                      @-}

{-@ inv            :: RBTree a -> {v:RBTree a | (Invs v)}   @-}
inv Leaf           = Leaf
inv (Node c x l r) = Node c x (inv l) (inv r)
