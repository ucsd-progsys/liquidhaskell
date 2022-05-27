module T1198_1 where

{-@ data Tree [sz] @-}
data Tree a =  Bin | Node (Tree a) (Tree a)

{-@ measure sz @-}
sz :: Tree a -> Int
sz Bin = 0 
sz (Node t1 t2) = 1 + sz t1 + sz  t2
