{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
module GHC.Internal.Int_LHAssumptions where

{-@
embed GHC.Internal.Int.Int8  as int
embed GHC.Internal.Int.Int16 as int
embed GHC.Internal.Int.Int32 as int
embed GHC.Internal.Int.Int64 as int

@-}
