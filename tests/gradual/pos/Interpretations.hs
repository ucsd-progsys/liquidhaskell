-- | Sec 4 from Gradual Refinement Types 

module Interpretations where

{-@ f :: x:{Int | ?? } -> Int -> Int @-} 
f :: Int -> Int -> Int 
f = flip div

{-@ g :: Int -> x:{Int | ?? } -> Int @-} 
g :: Int -> Int -> Int 
g = div 

{-@ h :: x:{Int | ?? } -> y:{Int | ?? } -> z:{Int |  ?? } -> Int @-} 
h :: Int -> Int -> Int -> Int 
h x y z = div (x + y) z