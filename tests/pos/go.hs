module Moo (poop) where

{-@ qualif Sum(v:Int, x: Int, y: Int): v = x + y @-}

{-@ foo  :: x:Int -> {v:Int | v = x} @-}
foo x    = go x 0
  where 
    go     :: Int -> Int -> Int 
    go 0 m = m
    go n m = go (n-1) (m+1)


poop x = foo x 
