{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--no-termination" @-}
module Class () where

import Language.Haskell.Liquid.Prelude

{-@ class measure sz :: forall a. a -> Int @-}

{-@ class Sized s where
      size :: forall a. x:s a -> {v:Nat | v = sz x}
  @-}
class Sized s where
  size :: s a -> Int

instance Sized [] where
  {-@ instance measure sz :: [a] -> Int
      sz ([])   = 0
      sz (x:xs) = 1 + (sz xs)
    @-}

  size []     = 0
  size (x:xs) = 1 + size xs

-- The following is needed to make this work (but are invariants checked?) 
{- invariant {v:[a] | sz v == len v} @-}

{-@ class (Sized s) => Indexable s where
      index :: forall a. x:s a -> {v:Nat | v < sz x} -> a
  @-}
class (Sized s) => Indexable s where
  index :: s a -> Int -> a


instance Indexable [] where
  index = (!!)

