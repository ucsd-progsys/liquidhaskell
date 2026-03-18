-- EmptySig.hs
-- Recovered parsing test for Issue #2020

{-@ LIQUID "--expect-error-containing=Cannot parse specification" @-}

module EmptySig where

{-@  :: foo -> x:Int -> {v:Int | v > x} @-}
foo :: Int -> Int 
foo x = x - 1
