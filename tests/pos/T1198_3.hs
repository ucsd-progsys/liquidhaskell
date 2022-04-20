module T1198_3 where

{-@ data Tree [sz] @-}
data Tree =  Bin | Node Tree Tree 

{-@ measure sz @-}
sz :: Tree -> Int
sz Bin = 0 
sz (Node t1 t2) = 1 + sz t1 + sz t2 
