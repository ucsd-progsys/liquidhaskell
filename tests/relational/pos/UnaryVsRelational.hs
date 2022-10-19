module Fixme where

{-@ reflect abs @-}
abs :: Int -> Int
abs x = if x < 0 then -x else x

{-@ relational abs ~ abs :: x1:Int -> Int ~ x2:Int -> Int
                         ~~ 0 <= x1 && x1 < x2 => r1 x1 < r2 x2 @-}

-- relational abs ~ abs checks => assume relationalAbsAbs

{-@ assume relationalAbsAbs :: x1:Int -> x2:Int -> {0 <= x1 && x1 < x2 => abs x1 < abs x2} @-}
relationalAbsAbs :: Int -> Int -> ()
relationalAbsAbs _ _ = ()

-- Interaction between unary and relational:
{-@ thm :: x:Nat -> {abs x < abs (x + 1)} @-}
thm :: Int -> ()
thm x = relationalAbsAbs x (x + 1)

