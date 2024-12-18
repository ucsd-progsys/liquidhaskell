{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Int_LHAssumptions where

import GHC.Int

{-@
embed Int8  as int
embed Int16 as int
embed Int32 as int
embed Int64 as int

type Nat64 = {v:Int64 | v >= 0}
@-}
