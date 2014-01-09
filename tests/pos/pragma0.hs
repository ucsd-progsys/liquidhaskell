{-@ LIQUID "--notermination" @-}

module Test0 () where


-- an obviously non-terminating function
zoo   :: Int -> Int
zoo x = zoo x
