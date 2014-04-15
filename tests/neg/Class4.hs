module Class4 where

import Language.Haskell.Liquid.Prelude

class Frog a where
  mkInt :: a -> Int
  mkInt _ = liquidAssert (1 < 0) 10

{-@ class Frog a where
      mkInt :: a -> Int
  @-}

-- If we put this in ANOTHER file (e.g. Class4Instance) then there is no error
instance Frog () where
