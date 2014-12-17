module Trees where

import Language.Haskell.Liquid.Prelude

data Tree a = Leaf a | Node [Tree a] 

{- data Tree a = Leaf a | Node { vv: [{v: Tree a | size v < sizes vv}]) @-}

{-@ data Tree a = Leaf (xx :: a) | Node (yy :: {vv : [{v:Tree a | size v < sizes vv}] | true}) @-}

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

{-@ tmap :: (a -> b) -> tt:Tree a -> Tree b / [size tt] @-}
tmap f tt = case tt of
             Leaf x  -> Leaf (f x)
             -- Node [] -> Node []
             -- Node (t:ts) -> Node (tmap f t : [])
             Node ts -> Node [tmap f (liquidAssume (0 <= size t && size t < size tt) t) | t <- ts]

