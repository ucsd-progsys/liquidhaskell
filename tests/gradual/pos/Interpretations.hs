-- | Sec 4 from Gradual Refinement Types 

module Interpretations where

{-@ f :: {v:Int | ?? } -> Int -> Int @-} 
f :: Int -> Int -> Int 
f = flip div

{-@ g :: Int -> {v:Int | ?? } -> Int @-} 
g :: Int -> Int -> Int 
g = div 

{-@ h :: {v:Int | ?? } -> {v:Int | ?? } -> {v:Int |  ?? } -> Int @-} 
h :: Int -> Int -> Int -> Int 
h x y z = div (x + y) z