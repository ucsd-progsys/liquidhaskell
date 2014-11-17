module RedBlack (ok) where

data RBTree a = Leaf 
              | Node Color a !(RBTree a) !(RBTree a)

data Color = B | R 

{-@ ok :: { v: RBTree Int | false} @-}
ok = Node R (2 :: Int)
         (Node B 1 Leaf Leaf)
         (Node B 3 Leaf Leaf)

{-@ data RBTree a = Leaf
                  | Node { c    :: Color
                         , key  :: a
                         , left :: RBTree a 
                         , left :: RBTree a 
                         }
  @-}


{- data RBTree a = Leaf
                  | Node { c    :: Color
                         , key  :: a
                         , left :: RBTree ({v:a | v < key})
                         , left :: RBTree ({v:a | key < v})
                         }
  -}
