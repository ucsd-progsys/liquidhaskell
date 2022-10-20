module Fixme where

isZero :: Int -> Bool
isZero 0 = True
isZero _ = False

{-@ reflect leq @-}
leq :: Bool -> Bool -> Bool
leq True False = False
leq _    _     = True

{-@ relational isZero ~ isZero :: x1:Nat -> Bool ~ x2:Nat -> Bool
                               | x1 <= x2 => Fixme.leq (r2 x2) (r1 x1) @-}
--                             | x1 < x2 => Fixme.leq (r2 x2) (r1 x1) @-} -- works
--                             | x1 == x2 => Fixme.leq (r2 x2) (r1 x1) @-} -- doesn't