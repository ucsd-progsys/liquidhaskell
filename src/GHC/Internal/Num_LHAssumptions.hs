{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
module GHC.Internal.Num_LHAssumptions where

import GHC.Num.Integer_LHAssumptions()

{-@
assume GHC.Internal.Num.fromInteger :: x:GHC.Num.Integer.Integer -> {v:a | v = x }

assume GHC.Internal.Num.negate :: (GHC.Internal.Num.Num a)
               => x:a
               -> {v:a | v = -x}

assume GHC.Internal.Num.abs :: (GHC.Internal.Num.Num a) => x:a -> {y:a | (x >= 0 ==> y = x) && (x < 0 ==> y = -x) }

assume GHC.Internal.Num.+ :: x:a -> y:a -> {v:a | v = x + y }
assume GHC.Internal.Num.- :: (GHC.Internal.Num.Num a) => x:a -> y:a -> {v:a | v = x - y }
@-}
