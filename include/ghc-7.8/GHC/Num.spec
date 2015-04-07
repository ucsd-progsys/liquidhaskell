module spec GHC.Num where

GHC.Num.fromInteger :: (GHC.Num.Num a)
                    => x:GHC.Integer.Type.Integer
                    -> {v:a | v = x }

GHC.Num.negate :: (GHC.Num.Num a)
               => x:a
               -> {v:a | v = -x}
