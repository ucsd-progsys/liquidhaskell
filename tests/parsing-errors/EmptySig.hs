-- This can't catch parse errors
{-@ LIQUID "--expect-error-containing=Cannot parse specification" @-}

module EmptySig where

{-@  :: foo -> x:Int -> {v:Int | v > x} @-}
foo :: Int -> Int 
foo x = x - 1
