{-@ LIQUID "--expect-any-error" @-}
module CaseOnRec where

data Parity = Even | Odd

{-@ f :: n:Int -> Parity / [if n >= 0 then n else -n] @-}
f :: Int -> Parity
f 0 = Even
f n = case f (if n < 0 then n + 1 else n - 1) of
  Even -> Odd
  Odd  -> Even

{-@ relational f ~ f :: {n1:_ -> _ ~ n2:_ -> _ 
                     | true :=> ((r1 n1 == r2 n2) <=> (((n1 - n2) mod 2) == 1))} @-}