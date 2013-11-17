\begin{code}
module Termination where
import Prelude hiding (sum)
type Value = Int

type Vec = Int -> Value

{-@ sum :: Vec -> Nat -> Value @-}
sum :: Vec -> Int -> Value
sum a 0 = a 0
sum a i = a i + sum a (i-1)

{-@ sum' :: Vec -> Value -> Nat -> Value @-}
sum' :: Vec -> Value -> Int -> Value
sum' a acc 0 = acc + a 0 
sum' a acc i = sum' a (acc + a i) (i-1)

{-@ Decrease sum' 3 @-}


type Vec2D = Int -> Int -> Value

{-@ sum2D :: Vec2D -> Nat -> Nat -> Value @-}
sum2D :: Vec2D -> Int -> Int -> Value
sum2D a n m = go n m
  where 
       {-@ Decrease go 1 2 @-}
       {-@ go :: i:Nat -> j:Nat -> Value / [i, j] @-}
        go 0 0 = a 0 0
        go i j | j == 0    =  a i 0 + go (i-1) m
               | otherwise =  a i j + go i (j-1)

{-@ sumFromTo :: Vec -> lo:Nat -> hi:{v:Nat|v>=lo} -> Value @-}
sumFromTo :: Vec -> Int -> Int ->  Value
sumFromTo a lo hi = go lo hi
  where 
       {-@ go :: lo:Nat -> hi:{v:Nat|v>=lo} -> Value / [hi-lo] @-}
        go lo hi | lo == hi  =  a lo
                 | otherwise =  a lo + go (lo+1) hi
\end{code}
