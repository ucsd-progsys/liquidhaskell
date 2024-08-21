{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
module Liquid.Prelude.Real_LHAssumptions where

import GHC.Num()

{-@
assume GHC.Internal.Num.* :: (GHC.Internal.Num.Num a) => x:a -> y:a -> {v:a | v = x * y} 
@-}
