module Div where

{-@ LIQUID "--real" @-}


{-@ type Valid = {v:Bool | ( (Prop v) <=> true ) } @-}

{-@ mulAssoc :: (Eq a, Fractional a) => a -> a -> a -> Valid @-}
mulAssoc :: (Eq a, Fractional a) => a -> a -> a -> Bool
mulAssoc x y z = (x * y) * z == x * (y * z) 

{-@ mulCommut :: (Eq a, Fractional a) => a -> a -> Valid @-}
mulCommut :: (Eq a, Fractional a) => a -> a -> Bool
mulCommut x y = x * y == y * x 

{-@ mulId :: (Eq a, Fractional a) => a -> Valid @-}
mulId :: (Eq a, Fractional a) => a -> Bool
mulId x = x == 1 * x 

{-@ mulDistr :: Double -> Double -> Double -> Valid @-}
mulDistr :: Double -> Double -> Double -> Bool
mulDistr x y z = x * (y + z)  == (x * y) + (x * z)

{-@ divId :: Double -> Valid @-}
divId :: Double -> Bool
divId x = x / 1.0 == x

{-@ inverse :: {v:Double | v != 0.0} -> Valid @-}
inverse :: Double -> Bool
inverse x = 1.0 == x * (1.0 / x)
