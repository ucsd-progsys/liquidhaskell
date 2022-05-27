{-@ LIQUID "--prune-unsorted" @-}

module Propability where

{-@ type Boolability = {v:Double | ((0.0 <= v) && (v <= 1.0)) } @-}

{-@ p :: Boolability @-}
p :: Double
p = 0.8

data DPD k = DPD [Pair k Double]

data Pair x y = P x y
{-@ data DPD k = DPD (val::{v:[Pair k Boolability]|(total v) = 1.0 }) @-}

{-@ measure total @-}
total :: [Pair k Double] -> Double
total [] = 0.0
total (x:xs) = (sndP x) + (total xs)

{-@ measure sndP @-} 
sndP :: Pair x Double -> Double
sndP (P x y) = y

dpd0 :: DPD Int
dpd0 = DPD [P 1 0.8, P 2 0.1, P 3 0.1]
