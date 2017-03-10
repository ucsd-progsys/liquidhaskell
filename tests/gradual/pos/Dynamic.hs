-- | Sec 5 from Gradual Refinement Types 

module Interpretations where
{-@ LIQUID "--gradual" @-}
{-@ LIQUID "--eliminate=none" @-}

{-@ f :: {v:Int | 0 < v } -> Int @-} 
f :: Int -> Int 
f = undefined  


{-@ g :: x:{Int | ?? } -> y:{Int | x <= y } -> Int @-} 
g :: Int -> Int -> Int 
g x y = f y + x 