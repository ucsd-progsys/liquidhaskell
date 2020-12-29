
module Fixme where 

{-@ add :: x:Int -> y:Int -> {v:Int|v = x + y} @-}
add :: Int -> Int -> Int
add = (+)

{-@ incr :: x:Int -> {v:Int|v = x + 1} @-}
incr :: Int -> Int 
incr x = let one = 1 in add x one

incrf :: Int -> Int
incrf x = let tmp = \f -> add (f x) 1 in tmp incr

{-@ type Pos = {v:Int|v > 0} @-}

{-@ relational incrf ~ incrf 
        :: x1:Nat -> Pos ~ x2:Nat -> Pos
        ~~ x1 == x2 => r1 x1 == r2 x2      @-}

