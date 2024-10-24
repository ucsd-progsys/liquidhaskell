{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Liquid.Prelude.Real_LHAssumptions where

import GHC.Internal.Num

{-@
assume GHC.Internal.Num.* :: Num a => x:a -> y:a -> {v:a | v = x * y} 
@-}
