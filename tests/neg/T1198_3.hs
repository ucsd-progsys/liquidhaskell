{-@ LIQUID "--expect-any-error" @-}
module T1198_3 where

{-@ data Tree [sz] @-}
data Tree a =  Bin | Node (Tree a) (Tree a)

{-@ measure sz @-}
sz :: Tree a -> Int
sz Bin = 0 
sz (Node t1 t2) = 1 + sz  (Node t1 t2) + sz  t2
