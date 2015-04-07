module spec Prelude where

import GHC.Num

assume GHC.Num.* :: (GHC.Num.Num a) => x:a -> y:a -> {v:a | v = x * y} 



GHC.Real./       :: (GHC.Real.Fractional a) => x:a -> y:{v:a | v != 0.0} -> {v: a | v = (x / y) }
