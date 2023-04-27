module GHC.Num_LHAssumptions where

{-@
embed GHC.Integer.Type.Integer as int
embed GHC.Num.Integer as int

assume GHC.Num.fromInteger :: (GHC.Num.Num a) => x:Integer -> {v:a | v = x }

assume GHC.Num.negate :: (GHC.Num.Num a)
               => x:a
               -> {v:a | v = -x}

assume GHC.Num.abs :: (GHC.Num.Num a) => x:a -> {y:a | (x >= 0 ==> y = x) && (x < 0 ==> y = -x) }

assume GHC.Num.+ :: (GHC.Num.Num a) => x:a -> y:a -> {v:a | v = x + y }
assume GHC.Num.- :: (GHC.Num.Num a) => x:a -> y:a -> {v:a | v = x - y }
@-}
