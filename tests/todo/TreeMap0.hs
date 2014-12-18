module Trees where

{- LIQUID "--no-termination" @-}

import Language.Haskell.Liquid.Prelude

data Tree a = Leaf a | Node [Tree a] 

{-@ data Tree a = Leaf (xx :: a) | Node (yy :: {mickeymouse : [{v:Tree a | size v < sizes mickeymouse}] | true}) @-}

{-@ measure size  @-}
{-@ measure sizes  @-}

{-@ invariant {v: [Tree a] | sizes v >= 0  } @-}
{-@ invariant {v: Tree a | size v >= 0  } @-}

{-@ size           :: t:Tree a -> {v:Nat | v = size t} / [size t, 0] @-}
size :: Tree a -> Int
size (Leaf _)  = 1
size (Node xs) = 1 + sizes xs

{-@ sizes         :: xs:[Tree a] -> {v:Nat | v = sizes xs} / [sizes xs, len xs] @-}
sizes :: [Tree a ] -> Int
sizes []      = 0
sizes (t:ts)  = size t + sizes ts

{- data Tree a [sizes] @-}

foo tt = case tt of
           Leaf x  -> () 
           Node ts -> liquidAssert (1 + sizes ts == size tt) ()

{-@ tmap :: _ -> tt:Tree a -> Tree a / [size tt] @-}
tmap f tt = case tt of
             Leaf x  -> Leaf x
             Node ts -> Node (goo tt ts)

{-@ goo :: tt:Tree a -> [{v: Tree a | size v < size tt}] -> [Tree a] @-}
goo :: Tree a -> [Tree a] -> [Tree a]
goo tt [] = []
goo tt (t:ts) = t : goo tt ts


             -- Node ts -> liquidAssert (sizes ts < size tt) (Node [])
             -- Node ts -> Node [liquidAssert (size t < size tt) t | t <- ts]
             -- Node ts -> Node [liquidAssert (size t < sizes ts) t | t <- ts]


{- maps :: (a -> b) -> tt:Tree a -> ts:[{v:Tree a | size v < size tt}] -> [Tree b] / [size tt, len ts] @-} 
-- maps _ _  []     = []
-- maps f tt (t:ts) = tmap f t : maps f tt ts

{-@ qualif SZ(v:a, x:b): size v < size x @-}
