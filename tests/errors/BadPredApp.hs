module Boo where

{-@ data X <q :: Int -> Int -> Bool> = X (x0 :: Int) (x1 :: Int<q x0>) @-}  
data X = X Int Int  

{-@ data T <p :: Int -> Int -> Int -> Int -> Bool> = C { x :: Int, y :: Int, z :: X<p x y> } @-}
data T = C { x :: Int, y :: Int, z :: X }  
