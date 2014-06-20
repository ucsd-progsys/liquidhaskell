module spec Prelude where

import GHC.Num
assume GHC.Num.* :: (GHC.Num.Num a) => x:a -> y:a 
                 -> {v:a | ((((((x = 0) || (y = 0)) => (v = 0))) 
                         && (((x > 0) && (y > 0)) => ((v >= x) && (v >= y))))
                         && (((x > 1) && (y > 1)) => ((v > x) && (v > y))))
                    }


GHC.Real./       :: (GHC.Real.Fractional a) => x:a -> y:{v:a | v != 0.0} -> a
