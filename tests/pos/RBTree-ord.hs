
{-@ LIQUID "--no-termination"   @-}

module Foo (add, remove, deleteMin, deleteMin') where

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

{-@ add :: (Ord a) => a -> ORBT a -> ORBT a @-}
add x s = makeBlack (ins x s)

{-@ ins :: (Ord a) => a -> ORBT a -> ORBT a @-}
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

{-@ remove :: (Ord a) => a -> ORBT a -> ORBT a @-}
remove x t = makeBlack (del x t)

{-@ del              :: (Ord a) => a -> ORBT a -> ORBT a @-}
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

{-@ append  :: y:a -> ORBT {v:a | v < y} -> ORBT {v:a | y < v} -> ORBT a @-}
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

{-@ deleteMin  :: ORBT a -> ORBT a @-}
deleteMin (Leaf)         = Leaf
deleteMin (Node _ x l r) = makeBlack t
  where 
    (_, t)               = deleteMin' x l r


{-@ deleteMin' :: k:a -> ORBT {v:a | v < k} -> ORBT {v:a | k < v} -> (a, ORBT a) @-}
deleteMin' k Leaf r              = (k, r)
deleteMin' x (Node R lx ll lr) r = (k, Node R x l' r)   where (k, l') = deleteMin' lx ll lr 
deleteMin' x (Node B lx ll lr) r = (k, lbalS x l' r )   where (k, l') = deleteMin' lx ll lr 

---------------------------------------------------------------------------
-- | Rotations ------------------------------------------------------------
---------------------------------------------------------------------------

lbalS k (Node R x a b) r              = Node R k (Node B x a b) r
lbalS k l (Node B y a b)              = let t = rbal k l (Node R y a b) in t 
lbalS k l (Node R z (Node B y a b) c) = Node R y (Node B k l a) (rbal z b (makeRed c))
lbalS k l r                           = error "nein" 

rbalS k l (Node R y b c)              = Node R k l (Node B y b c)
rbalS k (Node B x a b) r              = let t = lbal k (Node R x a b) r in t 
rbalS k (Node R x a (Node B y b c)) r = Node R y (lbal x (makeRed a) b) (Node B k c r)
rbalS k l r                           = error "nein"

lbal k (Node R y (Node R x a b) c) r  = Node R y (Node B x a b) (Node B k c r)
lbal k (Node R x a (Node R y b c)) r  = Node R y (Node B x a b) (Node B k c r)
lbal k l r                            = Node B k l r

rbal x a (Node R y b (Node R z c d))  = Node R y (Node B x a b) (Node B z c d)
rbal x a (Node R z (Node R y b c) d)  = Node R y (Node B x a b) (Node B z c d)
rbal x l r                            = Node B x l r

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

makeRed (Node _ x l r) = Node R x l r
makeRed Leaf           = error "nein" 

makeBlack Leaf           = Leaf
makeBlack (Node _ x l r) = Node B x l r

---------------------------------------------------------------------------
-- | Specifications -------------------------------------------------------
---------------------------------------------------------------------------

-- | Ordered Red-Black Trees

{-@ type ORBT a = RBTree <{\root v -> v < root }, {\root v -> v > root}> a @-}

-- | Binary Search Ordering

{-@ data RBTree a <l :: a -> a -> Prop, r :: a -> a -> Prop>
            = Leaf
            | Node (c     :: Color)
                   (key   :: a)
                   (left  :: RBTree <l, r> (a <l key>))
                   (right :: RBTree <l, r> (a <r key>))
  @-}
