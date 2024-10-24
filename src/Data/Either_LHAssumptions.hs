{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.Either_LHAssumptions where

import GHC.Types_LHAssumptions()

{-@
measure isLeft :: Either a b -> Bool
  isLeft (Left x)  = true
  isLeft (Right x) = false
@-}
