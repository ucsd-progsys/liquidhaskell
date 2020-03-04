
module T1597 where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-@ reflect plus @-}
plus :: Double -> Double -> Double
plus x y = x + y

{-@ reflect rdiv @-}
{-@ rdiv :: Double -> {v:Double | v /= 0 } -> Double @-}
rdiv :: Double -> Double -> Double 
rdiv x y = x / y
