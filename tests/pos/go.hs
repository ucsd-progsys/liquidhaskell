module Moo (poop) where

{-@ invariant {v:Int | v >= 0} @-}

{-@ qualif Sum(v:Int, x: Int, y: Int): v = x + y @-}

{-@ invariant {v:Int | v >= 0} @-}

{-@ foo  :: x:Int -> {v:Int | v = x} @-}
foo x    = go x 0
  where 
    go     :: Int -> Int -> Int 
    go 0 m = m
    go n m = go (n-1) (m+1)


poop x = foo x 



