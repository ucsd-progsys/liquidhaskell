-- | lfMod/lfDiv are the integer modulus and division in the logic,
-- while infix / is real division (#2735).
module LfModLfDiv where

{-@ type Even = {v:Int | lfMod v 2 = 0} @-}

{-@ four :: Even @-}
four :: Int
four = 4

{-@ half :: x:{Int | x >= 0} -> {v:Int | v = lfDiv x 2} @-}
half :: Int -> Int
half x = x `div` 2

{-@ evenMod :: x:Int -> {v:Int | v = lfMod x 2} @-}
evenMod :: Int -> Int
evenMod x = x `mod` 2

{-@ halfReal :: x:Double -> {v:Double | v = x / 2.0} @-}
halfReal :: Double -> Double
halfReal x = x / 2
