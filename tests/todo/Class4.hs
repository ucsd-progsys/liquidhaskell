{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--no-termination" @-}

module Class4 where

import Language.Haskell.Liquid.Prelude

class Frog a where
  mkInt :: a -> Int
  mkInt _ = 0 - 10

{-@ class Frog a where
      mkInt :: a -> Nat
  @-}

-- If we put this in ANOTHER file (e.g. Class4Instance) then there is no error
-- instance Frog () where

{- class Frog a where 
    mkInt :: a -> Int @-}
