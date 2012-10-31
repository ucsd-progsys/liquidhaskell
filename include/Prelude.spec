module spec Prelude where

import GHC.Base
import GHC.List

assume GHC.Integer.smallInteger :: x:GHC.Prim.Int# -> {v:Integer | v = (x :: Integer)}
assume GHC.Num.+                :: (Num a) => x:a -> y:a -> {v:a | v = x + y }
assume GHC.Num.-                :: (Num a) => x:a -> y:a -> {v:a | v = x - y }
assume GHC.Num.*                :: (Num a) => x:a -> y:a -> {v:a | (((x >= 0) && (y >= 0)) => (v >= 0)) }
assume GHC.Real.div             :: (Integral a) => x:a -> y:a -> {v:a | v = (x / y) }
assume GHC.Real.mod             :: (Integral a) => x:a -> y:a -> {v:a | v = (x mod y) }
assume GHC.Real./               :: (Fractional a) => x:a -> y:{v:a | v != 0} -> {v: a | v = (x / y) }
assume GHC.Real.fromIntegral    :: (Integral a, Num b) => x: a -> {v: b | ((x != 0) => (v != 0))}
assume GHC.Num.fromInteger      :: (Num a) => x:Integer -> {v:a | v = x }




measure isJust :: forall a. Maybe a -> Bool 
isJust (Just x)  = true
isJust (Nothing) = false

measure fromJust :: forall a. Maybe a -> a 
fromJust (Just x) = x 

embed Integer  as int



