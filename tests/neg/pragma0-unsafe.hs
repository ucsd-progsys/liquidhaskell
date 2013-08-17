-- NO PRAGMA version of tests/pos/pragma0.hs

module Test0 where

-- an obviously non-terminating function

zoo   :: Int -> Int
zoo x = zoo x
