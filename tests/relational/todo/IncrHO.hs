module Fixme where

incr :: Int -> Int
incr = (+ 1)

{-@ reflect f @-}
f :: (Int -> Int) -> Int -> Int
f g x = g x

{-@ relational f ~ f :: { g1:(z1:Int -> Int) -> x1:Int -> Int 
                        ~ g2:(z2:Int -> Int) -> x2:Int -> Int
                        | !(z1 < z2 :=> r1 < r2) :=> x1 < x2 :=> r1 g1 x1 < r2 g2 x2 } @-}

{- HLINT ignore "Use camelCase" -}

{-@ relFF_rga :: g1:(z1:Int -> Int) -> g2:(z2:Int -> Int) -> lemmaG1G2:(z1:Int -> z2:{VV : Int | z1 < z2} -> {VV : () | g1 < g2}) -> x1:Int -> x2:{VV : Int | x1 < x2} -> {VV : () | Fixme.f g1 x1 < Fixme.f g2 x2} @-}
relFF_rga :: (Int -> Int)
          -> (Int -> Int)
          -> (Int -> Int -> ())
          -> Int
          -> Int
          -> ()
relFF_rga _ _ _ _ _ = ()