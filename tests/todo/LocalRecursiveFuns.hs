module Blank where

data Tree a = Tip | Node a (Tree a) (Tree a)

tmap                :: (a -> b) -> Tree a -> Tree b
tmap f Tip          = Tip
tmap f (Node x l r) = Node (f x) (tmap f l) (tmap f r)

-----------------------------------------------------------
{-@ union :: t1:(Tree a) -> t2:(Tree a) -> (Tree a) /[(sz t1) + (sz t2)] @-}
-- union :: Tree a -> Tree a -> Tree a
union Tip          t = t
union (Node x a b) t = Node x taa tbb
  where
    taa              = union ta a
    tbb              = union tb b
    (ta,  tb)        = split x t

-----------------------------------------------------------

{-@ split :: a -> t:Tree a -> (TreeLe a t, TreeLe a t) @-}
split :: a -> Tree a -> (Tree a, Tree a)
split = undefined

{-@ type TreeLe a T = {v:Tree a | (sz v) <= (sz T)} @-}

{-@ data Tree [sz]  @-}

{-@ measure sz      :: Tree a -> Int
    sz (Tip)        = 0
    sz (Node x l r) = 1 + (sz l) + (sz r)
  @-}
  
{-@ invariant {v:(Tree a) | (sz v) >= 0} @-}

{-@ qualif TreeLt(v:Tree a, t:Tree b): (sz v) < (sz t) @-}

