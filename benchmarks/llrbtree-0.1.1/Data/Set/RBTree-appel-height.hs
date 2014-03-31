
{-@ LIQUID "--no-termination"   @-}

module Foo where

import Language.Haskell.Liquid.Prelude

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

{-@ ins :: (Ord a) => a -> t:RBT a -> {v: ARBTN a {(bh t)} | ((IsB t) => (isRB v))} @-}
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

{-@ remove :: (Ord a) => a -> RBT a -> RBT a @-}
remove x t = makeBlack (del x t)

{-@ predicate HDel T V = (bh V) = (if (isB T) then (bh T) - 1 else (bh T)) @-}

{-@ del              :: (Ord a) => a -> t:RBT a -> {v:ARBT a | ((HDel t v) && ((isB t) || (isRB v)))} @-}
del x Leaf           = Leaf
del x (Node _ a y b) = case compare x y of
   EQ -> append a b 
   LT -> case a of
           Leaf         -> Node R Leaf y b
           Node B _ _ _ -> lbalS (del x a) y b
           _            -> let zoo = Node R (del x a) y b in zoo 
   GT -> case b of
           Leaf         -> Node R a y Leaf 
           Node B _ _ _ -> rbalS a y (del x b)
           _            -> Node R a y (del x b)

{-@ append                                  :: l:RBT a -> r:RBTN a {(bh l)} -> (ARBT2 a l r) @-}
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


{-@ deleteMin'                   :: l:RBT a -> a -> r:RBTN a {(bh l)} -> (a, ARBT2 a l r) @-}
deleteMin' Leaf k r              = (k, r)
deleteMin' (Node R ll lx lr) x r = (k, Node R l' x r)   where (k, l') = deleteMin' ll lx lr 
deleteMin' (Node B ll lx lr) x r = (k, lbalS l' x r )   where (k, l') = deleteMin' ll lx lr 

---------------------------------------------------------------------------
-- | Rotations ------------------------------------------------------------
---------------------------------------------------------------------------

{-@ lbalS                             :: l:ARBT a -> a -> r:RBTN a {1 + (bh l)} -> {v: ARBTN a {1 + (bh l)} | ((IsB r) => (isRB v))} @-}
lbalS (Node R a x b) k r              = Node R (Node B a x b) k r
lbalS l k (Node B a y b)              = let zoo = rbal l k (Node R a y b) in zoo 
lbalS l k (Node R (Node B a y b) z c) = Node R (Node B l k a) y (rbal b z (makeRed c))
lbalS l k r                           = liquidError "nein" -- Node R l k r

{-@ rbalS                             :: l:RBT a -> a -> r:ARBTN a {(bh l) - 1} -> {v: ARBTN a {(bh l)} | ((IsB l) => (isRB v))} @-}
rbalS l k (Node R b y c)              = Node R l k (Node B b y c)
rbalS (Node B a x b) k r              = let zoo = lbal (Node R a x b) k r in zoo
rbalS (Node R a x (Node B b y c)) k r = Node R (lbal (makeRed a) x b) y (Node B c k r)
rbalS l k r                           = liquidError "nein" -- Node R l k r

{-@ lbal                              :: l:ARBT a -> a -> RBTN a {(bh l)} -> RBTN a {1 + (bh l)} @-}
lbal (Node R (Node R a x b) y c) k r  = Node R (Node B a x b) y (Node B c k r)
lbal (Node R a x (Node R b y c)) k r  = Node R (Node B a x b) y (Node B c k r)
lbal l k r                            = Node B l k r

{-@ rbal                              :: l:RBT a -> a -> ARBTN a {(bh l)} -> RBTN a {1 + (bh l)} @-}
rbal a x (Node R b y (Node R c z d))  = Node R (Node B a x b) y (Node B c z d)
rbal a x (Node R (Node R b y c) z d)  = Node R (Node B a x b) y (Node B c z d)
rbal l x r                            = Node B l x r

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{-@ type BlackRBT a = {v: RBT a | ((IsB v) && (bh v) > 0)} @-}

{-@ makeRed :: l:BlackRBT a -> ARBTN a {(bh l) - 1} @-}
makeRed (Node _ l x r) = Node R l x r
makeRed Leaf           = liquidError "nein" 

{-@ makeBlack :: ARBT a -> RBT a @-}
makeBlack Leaf           = Leaf
makeBlack (Node _ l x r) = Node B l x r

---------------------------------------------------------------------------
-- | Specifications -------------------------------------------------------
---------------------------------------------------------------------------

{-@ data RBTree a <l :: a -> a -> Prop, r :: a -> a -> Prop>
      = Leaf 
      | Node (color :: Color) 
             (left  :: RBTree <l, r> (a <l key>) 
             (key   :: a) 
             (right :: RBTree <l, r> (a <r key>) 
  @-}
  
-- | Red-Black Trees

{-@ type RBT a    = {v: (RBTree a) | ((isRB v) && (isBH v)) } @-}
{-@ type RBTN a N = {v: (RBT a) | (bh v) = N }                @-}

{-@ measure isRB        :: RBTree a -> Prop
    isRB (Leaf)         = true
    isRB (Node c l x r) = ((isRB l) && (isRB r) && ((Red c) => ((IsB l) && (IsB r))))
  @-}

-- | Almost Red-Black Trees

{-@ type ARBT a    = {v: (RBTree a) | ((isARB v) && (isBH v))} @-}
{-@ type ARBTN a N = {v: (ARBT a)   | (bh v) = N }             @-}

{-@ measure isARB        :: (RBTree a) -> Prop
    isARB (Leaf)         = true 
    isARB (Node c l x r) = ((isRB l) && (isRB r))
  @-}

-- | Conditionally Red-Black Tree

{-@ type ARBT2 a L R = {v:ARBTN a {(bh L)} | (((IsB L) && (IsB R)) => (isRB v))} @-}

-- | Color of a tree

{-@ measure col         :: RBTree a -> Color
    col (Node c l x r)  = c
    col (Leaf)          = B
  @-}

{-@ measure isB        :: RBTree a -> Prop
    isB (Leaf)         = false
    isB (Node c l x r) = c == B 
  @-}

{-@ predicate IsB T = not (Red (col T)) @-}
{-@ predicate Red C = C == R            @-}

-- | Black Height

{-@ measure isBH        :: RBTree a -> Prop
    isBH (Leaf)         = true
    isBH (Node c l x r) = ((isBH l) && (isBH r) && (bh l) = (bh r))
  @-}

{-@ measure bh        :: RBTree a -> Int
    bh (Leaf)         = 0
    bh (Node c l x r) = (bh l) + (if (c == R) then 0 else 1) 
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
inv (Node c l x r) = Node c (inv l) x (inv r)
