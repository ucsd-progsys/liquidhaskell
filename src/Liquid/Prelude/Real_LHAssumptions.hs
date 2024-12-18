{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Liquid.Prelude.Real_LHAssumptions where

{-@
assume * :: Num a => x:a -> y:a -> {v:a | v = x * y}
@-}
