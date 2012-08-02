module spec Prelude where

import GHC.Base


assume GHC.Integer.smallInteger :: x:GHC.Prim.Int# -> {v:Integer | v = (x :: Integer)}
assume GHC.Num.+                :: (Num a) => x:a -> y:a -> {v:a | v = x + y }
assume GHC.Num.-                :: (Num a) => x:a -> y:a -> {v:a | v = x - y }
assume GHC.Num.*                :: (Num a) => x:a -> y:a -> {v:a | (((x >= 0) && (y >= 0)) => (v >= 0)) }
assume GHC.Real.div             :: (Integral a) => x:a -> y:a -> {v:a | v = (x / y) }
assume GHC.Real./               :: (Fractional a) => x:a -> y:{v:a | v != 0} -> {v: a | v = (x / y) }
assume GHC.Real.fromIntegral    :: (Integral a, Num b) => x: a -> {v: b | ((x != 0) => (v != 0))}
assume GHC.Num.fromInteger      :: (Num a) => x:Integer -> {v:a | v = x }
