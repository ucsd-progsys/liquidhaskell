module Alias00 where

{-@ type RealUp Thing = {v:Int | Thing < v} @-}

{-@ type Up Paw = RealUp Paw @-}

{-@ inc :: x:Int -> (Up x) @-} 
inc :: Int -> Int 
inc x = x + 1
