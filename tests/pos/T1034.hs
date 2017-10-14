{-@ LIQUID "--higherorder" @-}
module Iso where

data P a b  = P {p1 :: a, p2 :: b}
{-@ data P a b = P {p1 :: a, p2 :: b}@-}

{-@ type P1X a b X = {v:P a b | p1 v == X} @-}

{-@ check :: x:a -> P1X a b x -> b @-}
check :: a -> P a b -> b
check x (P y p) = p

-- THIS IS SAFE
{-@ ex1 :: P a b -> b @-}
ex1 ::  (P a b) -> b
ex1 f@(P y _) =
  check y f

-- This is UNSAFE
{-@ ex2 :: P a b -> b @-}
ex2 ::  (P a b) -> b
ex2 f =
  let (P y p) = f in check y f
  -- THIS IS OK: case f of (P y p) -> check y f

{-@ qualif Zonk(v:(P a b), x: a): (p1 v = x) @-}
