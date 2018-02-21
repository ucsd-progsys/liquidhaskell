module Term where

{-@ data Tree [sz] @-}
data Tree a = Leaf a | Node (Tree a) (Tree a)

{-@ measure sz @-}
sz :: a -> Tree a -> Int
sz _ (Leaf _) = 0
sz x (Node t1 t2) = 1 + sz x t1 + sz x t2