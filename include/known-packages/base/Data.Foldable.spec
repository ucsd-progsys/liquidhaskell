module spec Data.Foldable where

import GHC.Base

length :: Data.Foldable.Foldable f => forall a. xs:f a -> {v:Nat | v = len xs}
null   :: Data.Foldable.Foldable f => v:(f a) -> {b:Bool | (b <=> len v = 0) && (not b <=> len v > 0)}
