{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Int_LHAssumptions where

import GHC.Int

{-@
embed GHC.Internal.Int.Int8  as int
embed GHC.Internal.Int.Int16 as int
embed GHC.Internal.Int.Int32 as int
embed GHC.Internal.Int.Int64 as int

type Nat64 = {v:GHC.Internal.Int.Int64 | v >= 0}
@-}
