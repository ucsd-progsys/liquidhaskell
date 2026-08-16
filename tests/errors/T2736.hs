{-@ LIQUID "--expect-error-containing=The decreasing parameters should be of same type" @-}

-- sizeTree, sizeForest and sizeTrees recurse on a Tree, a Forest and a list, so
-- no single size function covers the group.
module T2736 where

data Tree = Leaf Int | Node Forest

data Forest = Forest
  { label :: Int
  , trees :: [Tree] }

{-@ autosize Tree @-}
{-@ autosize Forest @-}

sizeTree :: Tree -> Int
sizeTree (Leaf _)   = 1
sizeTree (Node frs) = 1 + sizeForest frs

sizeForest :: Forest -> Int
sizeForest (Forest _ ts) = 1 + sizeTrees ts

sizeTrees :: [Tree] -> Int
sizeTrees []       = 0
sizeTrees (t : ts) = sizeTree t + sizeTrees ts
