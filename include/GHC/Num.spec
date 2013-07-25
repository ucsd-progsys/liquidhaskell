module spec GHC.Num where

assume GHC.Num.fromInteger      :: (Num a) => x:Integer -> {v:a | v = x }
