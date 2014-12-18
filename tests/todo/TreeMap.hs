module Trees where

{- LIQUID "--no-termination" @-}

import Language.Haskell.Liquid.Prelude

data Tree a = Leaf a | Node [Tree a] 

{-@ data Tree a = Leaf (xx :: a) | Node (subtrees :: {vv : [{v:Tree a | size v < sizes vv}] | true}) @-}

{-@ measure size  @-}
{-@ measure sizes  @-}

{-@ invariant {v: [Tree a] | (sizes v) >= (size (head v))  } @-}
{-@ invariant {v: [Tree a] | sizes v >= 0  } @-}
{-@ invariant {v: Tree a | size v >= 0  } @-}



{-@ measure head :: [a] -> a 
    head (x:xs) = x
  @-}

{-@ size           :: x:Tree a -> {v:Nat | v = size x} / [size x, 0] @-}
size :: Tree a -> Int
size (Leaf _)  = 1
size (Node xs) = 1 + sizes xs

{-@ sizes         :: xs:[Tree a] -> {v:Nat | v = sizes xs} / [sizes xs, len xs] @-}
sizes :: [Tree a ] -> Int
sizes []      = 0
sizes (t:ts)  = size t + sizes ts

{- data Tree a [sizes] @-}

{-@ tmap :: _ -> tt:Tree a -> Tree b / [size tt, 1, 0] @-}
-- tmap f tt = case tt of
tmap f (Leaf x) = Leaf (f x)
tmap f tt@(Node ts) = Node (goo f (Node ts) (lemmasize (Node ts))) -- [liquidAssert (size t < size tt) t | t <- ts]

{-@ Lazy lemmasize @-}
{-@ lemmasize :: tt:Tree a -> [{v:Tree a | size v < size tt}] @-}
lemmasize :: Tree a  -> [Tree a]
lemmasize (Node (t:ts)) = t : lemmasize (Node ts)


{-@ goo :: (a -> b) -> tt:Tree a -> ts:[{v: Tree a | size v < size tt}] -> [Tree b] / [size tt, 0, len ts] @-}
goo :: (a -> b) -> Tree a -> [Tree a] -> [Tree b]
goo f tt [] = []
goo f tt (t:ts) = tmap f t : goo f tt ts

{- maps :: (a -> b) -> tt:Tree a -> ts:[{v:Tree a | size v < size tt}] -> [Tree b] / [size tt, len ts] @-} 
-- maps _ _  []     = []
-- maps f tt (t:ts) = tmap f t : maps f tt ts

{-@ qualif SZ(v:Tree a, x:Tree a): size v < size x @-}

{-@ qual :: xs:[Tree a] -> {v:Tree a | size v = 1 + (sizes xs)} @-}
qual :: [Tree a] -> Tree a
qual = undefined

{- qualif SZ1(v:Tree a, xs:List (Tree a)): size v = 1 + (sizes xs) @-}
