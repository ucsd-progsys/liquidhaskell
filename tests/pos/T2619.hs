{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

{-@ LIQUID "--save" @-}
module T2619 where

{-@ foo :: x:p -> y:{p | y /= 0.0} -> {(x/y) * y == x} @-}
foo :: Fractional p => p -> p -> ()
foo _ _  = ()

{-@ bar :: num:Double -> {den:Double | den /= 0} -> {(num/den) * den == num} @-}
bar :: Double -> Double -> ()
bar _ _ = ()
