{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.Foldable_LHAssumptions where

import Data.Foldable
import GHC.Types_LHAssumptions()
import Prelude hiding (length, null)

{-@
assume length :: Foldable f => forall a. xs:f a -> {v:Nat | v = len xs}
assume null   :: Foldable f => forall a. v:(f a) -> {b:Bool | (b <=> len v = 0) && (not b <=> len v > 0)}
@-}
