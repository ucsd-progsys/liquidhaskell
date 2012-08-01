module spec Prelude where

import GHC.Base

assume GHC.Integer.smallInteger :: x:GHC.Prim.Int# -> {v:Integer | v = (x :: Integer)}
assume GHC.Num.+                :: (Num a) => x:a -> y:a -> {v:a | v = x + y }
assume GHC.Num.-                :: (Num a) => x:a -> y:a -> {v:a | v = x - y }
assume GHC.Num.*                :: (Num a) => x:a -> y:a -> {v:a | (((x >= 0) && (y >= 0)) => (v >= 0)) }
assume GHC.Real.div             :: (Integral a) => x:a -> y:a -> {v:a | v = (x / y) }
assume GHC.Num.fromInteger      :: (Num a) => x:Integer -> {v:a | v = x }
