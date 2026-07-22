{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Num_LHAssumptions where

import GHC.Num
import GHC.Num.Integer_LHAssumptions()

{-@
assume fromInteger :: (Num a) => x:Integer -> {v:a | v = x }

assume negate :: (Num a)
               => x:a
               -> {v:a | v = -x}

assume abs :: (Num a) => x:a -> {y:a | (x >= 0 ==> y = x) && (x < 0 ==> y = -x) }

define abs x = if x >=0 then x else -x

assume + :: (Num a) => x:a -> y:a -> {v:a | v = x + y }
assume - :: (Num a) => x:a -> y:a -> {v:a | v = x - y }
@-}
