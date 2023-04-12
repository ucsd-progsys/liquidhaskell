module Data.Foldable_LHAssumptions where

import GHC.Types_LHAssumptions()

{-@
assume Data.Foldable.length :: Data.Foldable.Foldable f => forall a. xs:f a -> {v:Nat | v = len xs}
assume Data.Foldable.null   :: Data.Foldable.Foldable f => v:(f a) -> {b:Bool | (b <=> len v = 0) && (not b <=> len v > 0)}
@-}
