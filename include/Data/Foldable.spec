module spec Data.Foldable where

import GHC.Base

assume length :: Data.Foldable.Foldable f => xs:f a -> {v:Nat | v = len xs}

assume concat :: Data.Foldable.Foldable f => xs:f [a] -> {v:[a] | len v = sumLens xs}
