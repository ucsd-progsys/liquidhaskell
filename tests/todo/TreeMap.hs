module Trees where

data Tree a = Leaf a | Node [Tree a]

{-@ measure size  @-}
{-@ size           :: Tree a -> Nat @-}
size (Leaf _)  = 1
size (Node xs) = sizes xs

{-@ measure sizes @-}
{-@ sizes     :: [Tree a] -> Nat @-}
sizes         :: [Tree a] -> Int
sizes []      = 0
sizes (t:ts)  = size t + sizes ts

{- data Tree a [sizes] @-}

{-@ tmap :: (a -> b) -> t:Tree a -> Tree b / [size t] @-}
tmap f (Leaf x)  = Leaf (f x)
tmap f (Node ts) = Node (map (tmap f) ts)

