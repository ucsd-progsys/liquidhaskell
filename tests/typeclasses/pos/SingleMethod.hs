{-@ LIQUID "--typeclass" @-}
module SingleMethod where

class HasNat a where
  {-@ nat :: a -> Nat @-}
  nat :: a -> Int

instance HasNat Bool where
  nat False = 0
  nat True  = 1


