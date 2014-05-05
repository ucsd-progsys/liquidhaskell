{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--no-termination" @-}

module Class4 where

import Language.Haskell.Liquid.Prelude

class Frog a where
  mkInt :: a -> Int
  mkInt _ = liquidAssert (0 > 1) 10


instance Frog Int where

{-@ mkInt :: (Frog a) => a -> Int @-}
