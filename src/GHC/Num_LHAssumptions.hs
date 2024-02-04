{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
module GHC.Num_LHAssumptions where

{-@
embed GHC.Num.Integer.Integer as int

assume GHC.Internal.Num.fromInteger :: (GHC.Internal.Num.Num a) => x:GHC.Num.Integer.Integer -> {v:a | v = x }

assume GHC.Internal.Num.negate :: (GHC.Internal.Num.Num a)
               => x:a
               -> {v:a | v = -x}

assume GHC.Internal.Num.abs :: (GHC.Internal.Num.Num a) => x:a -> {y:a | (x >= 0 ==> y = x) && (x < 0 ==> y = -x) }

assume GHC.Internal.Num.+ :: (GHC.Internal.Num.Num a) => x:a -> y:a -> {v:a | v = x + y }
assume GHC.Internal.Num.- :: (GHC.Internal.Num.Num a) => x:a -> y:a -> {v:a | v = x - y }
@-}
