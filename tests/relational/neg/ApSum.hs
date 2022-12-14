{-@ LIQUID "--expect-any-error" @-}
module ApSum where

apsum :: Int -> Int -> Int
apsum n a = if n <= 0 then a else a + n + apsum (n - 1) a

{-@ relational apsum ~ apsum 
        :: {n1:Int -> a1:Int -> Int ~ n2:Int -> a2:Int -> Int
        | n1 == n2 :=> a1 <= a2 :=> r1 n1 a1 < r2 n2 a2} @-}

