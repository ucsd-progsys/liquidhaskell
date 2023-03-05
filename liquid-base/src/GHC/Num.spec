module spec GHC.Num where

embed GHC.Integer.Type.Integer as int
embed GHC.Num.Integer as int

GHC.Num.fromInteger :: (GHC.Num.Num a) => x:Integer -> {v:a | v = x }

GHC.Num.negate :: (GHC.Num.Num a)
               => x:a
               -> {v:a | v = -x}

GHC.Num.abs :: (GHC.Num.Num a) => x:a -> {y:a | (x >= 0 ==> y = x) && (x < 0 ==> y = -x) }

GHC.Num.+ :: (GHC.Num.Num a) => x:a -> y:a -> {v:a | v = x + y }
GHC.Num.- :: (GHC.Num.Num a) => x:a -> y:a -> {v:a | v = x - y }
