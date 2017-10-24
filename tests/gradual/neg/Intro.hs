-- | Sec 1 from Gradual Refinement Types 

module Intro where


checkPos :: Int -> Int 
{-@ checkPos :: {v:Int | 0 < v} -> {v:Int | 0 < v} @-}
checkPos x = x 

{-@ check :: {v:Int | true } -> {v:Bool | true } @-} 
check :: Int -> Bool 
check x = undefined 

safe x = if check x then checkPos x else checkPos (-x) 


a :: Int -> Bool 
{-@ a :: {v:Int | v < 0} -> Bool @-}
a = undefined


b :: Int -> Int 
{-@ b :: {v:Int | v < 10} -> Int @-}
b = undefined


{-@ g0 :: {v:Int | true } -> Int @-} 
g0 :: Int -> Int 
g0 x = if a x then 1 `div` x else b x 

{-@ g1 :: {v:Int | 0 < v && ?? } -> Int @-} 
g1 :: Int -> Int 
g1 x = if a x then 1 `div` x else b x 