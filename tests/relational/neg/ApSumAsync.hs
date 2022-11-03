{-@ LIQUID "--expect-any-error" @-}
module ApSumAsync where

apsum :: Int -> Int -> Int
apsum n a = if n <= 0 then a else a + n + apsum (n - 1) a

{-@ relational apsum ~ apsum
        :: {n1:Int -> a1:Nat -> Nat ~ n2:Int -> a2:Nat -> Nat
        | n1 <= n2 :=> a1 <= a2 :=> r1 n1 a1 <= r2 n2 a2} @-}

{- T_unary <: T_relational -}

foo :: Int -> Int
foo n = apsum n (-1)

{-@ relational foo ~ foo :: {n1:_ -> _ ~ n2:_ -> _
                         | n1 < n2 :=> r1 n1 <= r2 n2} @-}