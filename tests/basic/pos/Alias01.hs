module Alias01 where

{-@ predicate LessThan Thing V = Thing < V @-}

{-@ inc :: x:Int -> {v:Int | LessThan x v} @-} 
inc :: Int -> Int 
inc x = x + 1
