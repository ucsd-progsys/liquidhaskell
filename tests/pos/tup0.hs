module DepTup0 () where

{-@ type PlusOne = (Int, Int)<{\x v -> v > x}> @-}

{-@ plusOne :: PlusOne @-}
plusOne :: (Int, Int)
plusOne = (0, 1)

{-@ plusOnes :: Maybe PlusOne @-}
plusOnes :: Maybe (Int, Int) 
plusOnes = Just plusOne -- (0, 1) (5,6), (999,1000)]
