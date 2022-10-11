{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--exactdc" @-}
module T1404_3 where

data Peano = Z | S Peano

{-@ impossible :: {msg:_ | False} -> a @-}
impossible :: String -> a
impossible msg = error msg

{-@ foo :: {n : Peano | n /= Z} -> _ -> {False} @-}
foo :: Peano -> Peano -> a
foo (S n) m = bar n (S m)
foo _ _ = impossible "unreachable"

{-@ bar :: _ -> {n : Peano | n /= Z} -> {False} @-}
bar :: Peano -> Peano -> a
bar m (S n) = foo (S m) n
bar _ _ = impossible "unreachable"

{-@ oneIsTwo :: {1 == 2} @-}
oneIsTwo = foo (S Z) Z
