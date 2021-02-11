module Fixme where

apsum :: Int -> Int -> Int
apsum n a = if n <= 0 then a else a + n + apsum (n - 1) a

{-
        a1 <= a2 + n2 + apsum (n2 - 1) a2
-}

{-@ relational apsum ~ apsum
        :: n1:Int -> a1:Nat -> Nat ~ n2:Int -> a2:Nat -> Nat
        ~~ n1 <= n2 => a1 <= a2 => r1 n1 a1 <= r2 n2 a2 @-}
