-- NO PRAGMA version of tests/pos/pragma0.hs
-- an obviously non-terminating function

module Test0 where


zoo   :: Int -> Int
zoo 0 = 0
zoo x = zoo x
