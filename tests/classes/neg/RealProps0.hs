{-@ LIQUID "--expect-any-error" @-}

-- Issue overload-div-int-real #579

module RealProps0 where

divId :: Double -> Double 
divId x = x / 0.0

