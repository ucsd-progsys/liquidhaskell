module RedBlack (ok) where

data RBTree a = Leaf 
              | Node Color a !(RBTree a) !(RBTree a)

data Color = B | R 

ok :: RBTree Int

{-@ ok :: { v: RBTree Int | false} @-}
ok = Node R 2
         (Node B 1 Leaf Leaf)
         (Node B 3 Leaf Leaf)

{-@ data RBTree a <l :: a -> a -> Prop, r :: a -> a -> Prop>
            = Leaf
            | Node { c    :: Color
                   , key  :: a
                   , left :: RBTree <l, r> (a <l key>)
                   , left :: RBTree <l, r> (a <r key>) }
  @-}
