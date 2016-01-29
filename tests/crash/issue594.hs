module Boo where

{-@ data X <q :: Int -> Int -> Prop> = X (x0 :: Int) (x1 :: Int<q x0>) @-}  
data X = X Int Int  

{-@ data T <p :: Int -> Int -> Int -> Int -> Prop> = C { x :: Int, y :: Int, z :: X<p x y> } @-}
data T = C { x :: Int, y :: Int, z :: X }  
