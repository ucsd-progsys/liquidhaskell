{-@ LIQUID "--no-termination" @-}
module RedBlack  where

data RBTree a = Leaf 
              | Node Color a !(RBTree a) !(RBTree a)

data Color = B | R 

{-@ ok :: { v: RBTree Int | false} @-}
ok = Node R (2 :: Int)
         (Node B 1 Leaf Leaf)
         (Node B 3 Leaf Leaf)

{-@ measure size @-}
size :: RBTree a -> Int
size Leaf = 0
size (Node _ _ l r) = 1 + size l + size r


{-@ data RBTree a = Leaf
                  | Node { c     :: Color
                         , key   :: a
                         , left  :: RBTree ({v:a | v < key})
                         , right :: RBTree ({v:a | key < v})
                         }
  @-}
