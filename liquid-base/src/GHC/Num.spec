module spec GHC.Num where

embed GHC.Integer.Type.Integer as int 

GHC.Num.fromInteger :: (GHC.Num.Num a) => x:GHC.Integer.Type.Integer -> {v:a | v = x }

GHC.Num.negate :: (GHC.Num.Num a)
               => x:a
               -> {v:a | v = -x}

GHC.Num.+ :: (GHC.Num.Num a) => x:a -> y:a -> {v:a | v = x + y }
GHC.Num.- :: (GHC.Num.Num a) => x:a -> y:a -> {v:a | v = x - y }

// Taken from include/Real.spec
assume GHC.Num.* :: (GHC.Num.Num a) => x:a -> y:a -> {v:a | v = x * y} 
