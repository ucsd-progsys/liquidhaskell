{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
module GHC.Internal.Data.Foldable_LHAssumptions where

import GHC.Types_LHAssumptions()

{-@
assume GHC.Internal.Data.Foldable.length :: GHC.Internal.Data.Foldable.Foldable f => forall a. xs:f a -> {v:Nat | v = len xs}
assume GHC.Internal.Data.Foldable.null   :: GHC.Internal.Data.Foldable.Foldable f => forall a. v:(f a) -> {b:Bool | (b <=> len v = 0) && (not b <=> len v > 0)}
@-}
