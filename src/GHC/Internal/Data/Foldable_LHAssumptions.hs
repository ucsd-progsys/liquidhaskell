{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Internal.Data.Foldable_LHAssumptions where

import GHC.Internal.Data.Foldable
import GHC.Types_LHAssumptions()

{-@
assume GHC.Internal.Data.Foldable.length :: Foldable f => forall a. xs:f a -> {v:Nat | v = len xs}
assume GHC.Internal.Data.Foldable.null   :: Foldable f => forall a. v:(f a) -> {b:Bool | (b <=> len v = 0) && (not b <=> len v > 0)}
@-}
