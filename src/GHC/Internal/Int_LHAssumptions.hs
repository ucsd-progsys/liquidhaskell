{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Internal.Int_LHAssumptions where

import GHC.Internal.Int

{-@
embed Int8  as int
embed Int16 as int
embed Int32 as int
embed Int64 as int
@-}
