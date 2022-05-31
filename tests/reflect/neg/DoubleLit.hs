{-@ LIQUID "--expect-any-error" @-}
module DoubleLit where

{-@ inline absD @-}
absD :: Double -> Double
absD z = if z >= 0 then z else (0 - z)

{-@ inline absI @-}
absI :: Int -> Int
absI z = if z >= 0 then z else (0 - z)

{-@ zoing :: {v:Double | v = 3.14 } @-}
zoing :: Double
zoing = absD (4.15 - 6.29)
