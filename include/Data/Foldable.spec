module spec Data.Foldable where

import GHC.Base

assume length :: Data.Foldable.Foldable f => xs:f a -> {v:Nat | v = len xs}
