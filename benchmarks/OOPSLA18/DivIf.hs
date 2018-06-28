module Gradual (isPos) where
 

{-@ isPos :: Int -> Bool @-}
isPos :: Int -> Bool 
isPos = undefined 

divIf :: Int -> Int 
divInt :: Int -> Int -> Int 
{-@ divInt :: Int -> {v:Int | 0 < v } -> Int @-}
divInt = div 


qual :: Int -> Int -> Int 
{-@ qual :: Int -> {v:Int | false } -> Int @-}
qual = div 


{-@ divIf :: {v:Int | ??  } -> Int @-}
divIf x = if isPos x then 1 `divInt` x else 1 `divInt` (1-x)
