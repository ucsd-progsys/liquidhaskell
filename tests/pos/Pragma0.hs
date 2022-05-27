{-@ LIQUID "--notermination" @-}

module Pragma0 where


-- an obviously non-terminating function
zoo   :: Int -> Int
zoo x = zoo x
