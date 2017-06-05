module DPairs where


{-@ incrPair :: Int -> (x::Int, {v:Int | x <= v}) @-}
incrPair :: Int -> (Int, Int)
incrPair i = (i, i+1)


{-@ incrPair3 :: Int -> (x::Int, y::{v:Int | x <= v}, {v:Int | y <= v}) @-}
incrPair3 :: Int -> (Int, Int, Int)
incrPair3 i = (i, i+1, i+3)

{-@ assertDep :: (Int, Int)<\x -> {v:Int | x <= v}> -> {b:Bool | b} @-}
assertDep :: (Int, Int) -> Bool 
assertDep (x, y) = x <= y



{-@ goalDep :: (x::Int, {v:Int | x <= v}) -> {b:Bool | b} @-}
goalDep :: (Int, Int) -> Bool 
goalDep (x, y) = x <= y
