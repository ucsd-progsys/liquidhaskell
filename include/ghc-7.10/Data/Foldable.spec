module spec Data.Foldable where

class measure len :: forall a. a -> Int

length :: Data.Foldable.Foldable t => xs:t a -> {v:Nat | v = len xs}
