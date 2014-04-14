{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--no-termination" @-}

module Class where

import Language.Haskell.Liquid.Prelude

class Frog a where
  mkInt :: a -> Int
  mkInt _ = liquidAssert (1 > 0) 10


{-@ mkInt :: (Frog a) => a -> Int @-}
