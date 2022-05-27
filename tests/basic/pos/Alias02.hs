module Alias02 where

{-@ predicate Less X Y = X < Y @-} 

{-@ inc :: x:Int -> {v:Int | Less x v} @-} 
inc :: Int -> Int 
inc x = x + 1
