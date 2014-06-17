module Div where

{-@ LIQUID "--real" @-}


{-@ type Valid = {v:Bool | ( (Prop v) <=> true ) } @-}

{-@ mulAssoc :: Double -> Double -> Double -> Valid @-}
mulAssoc :: Double -> Double -> Double -> Bool
mulAssoc x y z = (x * y) * z == x * (y * z) 

{-@ mulCommut :: Double -> Double -> Valid @-}
mulCommut :: Double -> Double -> Bool
mulCommut x y = x * y == y * x 

{-@ mulId :: Double -> Valid @-}
mulId :: Double -> Bool
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
