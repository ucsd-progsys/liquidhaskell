{-@ LIQUID "--relational-hint" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module RIncr where

{-@ reflect incr @-}
incr :: Int -> Int
incr x = x + 1

--- Proof ---
{-@ relational incr ~ incr :: { xl : Int -> Int 
                              ~ xr : Int -> Int
                              | !(xl < xr) :=> r1 xl < r2 xr } @-}
--- End ---