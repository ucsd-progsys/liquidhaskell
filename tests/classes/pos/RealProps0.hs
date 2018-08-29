
-- Issue overload-div-int-real #579

module RealProps0 where

{-@ divId :: x:Double -> {v:Double | v = x} @-}
divId :: Double -> Double 
divId x = x / 1.0

