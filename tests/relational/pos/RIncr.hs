{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module RIncr () where

incr :: Int -> Int
incr x = x + 1

{-@ relational incr ~ incr :: { xl : Int -> Int 
                              ~ xr : Int -> Int
                              | xl < xr :=> r1 xl < r2 xr } @-}
