module Propability where


{- NIKI TO FIX:
   this should be SAFE but z3 doesnot like it because 
   snd :: Int -> Int instead of 
   snd :: Int -> Real 
-}

{-@ LIQUID "--real" @-}

{-@ type Propability = {v:Double | ((0.0 <= v) && (v <= 1.0)) } @-}

{-@ p :: Propability @-}
p :: Double
p = 0.8

{-@ q :: Propability @-}
q :: Double
q = 1.8



data DPD k = DPD [(k, Double)]

{-@ data DPD k = DPD (val::{v:[(k, Propability)]|(total v) = 1.0 }) @-}

{-@ measure total :: [(k, Double)] -> Double 
    total([]) = 0.0
    total(x:xs) = (snd x) + (total xs)
  @-}



dpd0 :: DPD Int
dpd0 = DPD [(1, 0.9), (2, 0.1)]

