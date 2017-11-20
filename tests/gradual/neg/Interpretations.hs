-- | Sec 4 from Gradual Refinement Types 

module Interpretations where

{-@ g :: Int -> {v:Int | v == 0 && ?? } -> Int @-} 
g :: Int -> Int -> Int 
g = div 


{-@ h :: {v:Int | ?? } -> {v:Int | ?? } -> {v:Int | v == 0 && ?? } -> Int @-} 
h :: Int -> Int -> Int -> Int 
h x y = div (x + y)


{-@ f :: {v:Int | ?? } -> Int -> Int @-} 
f :: Int -> Int -> Int 
f = div