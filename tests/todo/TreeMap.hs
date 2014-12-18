module Trees where

{- LIQUID "--no-termination" @-}

import Language.Haskell.Liquid.Prelude

data Tree a = Leaf a | Node [Tree a] 

{-@ data Tree a = Leaf (xx :: a) | Node (yy :: {vv : [{v:Tree a | size v < sizes vv}] | true}) @-}

{-@ measure size  @-}
{-@ measure sizes  @-}

{-@ invariant {v: [Tree a] | sizes v >= 0  } @-}
{-@ invariant {v: Tree a | size v >= 0  } @-}

{-@ size           :: x:Tree a -> Nat / [size x, 0] @-}
size :: Tree a -> Int
size (Leaf _)  = 1
size (Node xs) = 1 + sizes xs

{-@ sizes         :: xs:[Tree a] -> Nat / [sizes xs, len xs] @-}
sizes :: [Tree a ] -> Int
sizes []      = 0
sizes (t:ts)  = size t + sizes ts

{- data Tree a [sizes] @-}

{-@ tmap :: _ -> tt:Tree a -> Tree a @-}
tmap f tt = case tt of
             Leaf x  -> Leaf (x)
             Node ts -> Node (goo tt ts) -- [liquidAssert (size t < size tt) t | t <- ts]



{-@ goo :: tt:Tree a -> ts:[{v: Tree a | true}] -> [Tree a] / [len ts] @-}
goo :: Tree a -> [Tree a] -> [Tree a]
goo tt [] = []
goo tt (t:ts) = t : goo tt ts

{- maps :: (a -> b) -> tt:Tree a -> ts:[{v:Tree a | size v < size tt}] -> [Tree b] / [size tt, len ts] @-} 
-- maps _ _  []     = []
-- maps f tt (t:ts) = tmap f t : maps f tt ts

{-@ qualif SZ(v:Tree a, x:Tree a): size v < size x @-}
