module T1198_2 where

{-@ data Tree [sz] @-}
data Tree a =  Bin | Node (Tree a)

{-@ measure sz @-}
sz :: Tree a -> Int
sz Bin = 0 
sz (Node t1) = 1 + sz t1
