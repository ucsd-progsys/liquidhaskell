module Trees where

data Tree a = Leaf a | Node { kids :: [Tree a]} 

{-@ data Tree [sizes] a = Leaf {val :: a} | Node { kids :: {vv: [{v: (Tree a) | size v < sizes vv}]}} @-}

{-@ measure size  @-}
{-@ measure sizes  @-}

{-@ invariant {v: [Tree a] | sizes v >= 0  } @-}
{-@ invariant {v: Tree a | size v >= 0  } @-}

{-@ size           :: x:Tree a -> Nat / [size x, 0] @-}
size :: Tree a -> Int
size (Leaf x)  = 1
size (Node xs) = 1 + sizes xs

{-@ sizes         :: xs:[Tree a] -> Nat / [sizes xs, len xs] @-}
sizes :: [Tree a ] -> Int
sizes []      = 0
sizes (t:ts)  = size t + sizes ts

{- data Tree a [sizes] @-}

{-@ tmap :: (a -> b) -> t:Tree a -> Tree b / [size t] @-}
tmap f (Leaf x)  = Leaf (f x)
tmap f (Node ts) = Node (map (tmap f) ts)

