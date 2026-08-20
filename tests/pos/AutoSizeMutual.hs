module AutoSizeMutual where

{-@ autosize Tree @-}
{-@ autosize Forest @-}

data Tree   = Leaf Int | Node Forest
data Forest = Nil | Cons Tree Forest

-- The size of a Node counts the Forest under it and the size of a Cons counts
-- both of its fields, so the recursion below decreases on the Tree even where
-- it steps through the Forest.
sizeTree :: Tree -> Int
sizeTree (Leaf _)          = 0
sizeTree (Node Nil)        = 1
sizeTree (Node (Cons t f)) = 1 + sizeTree t + sizeTree (Node f)
