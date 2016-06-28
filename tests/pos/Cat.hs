{-# LANGUAGE GADTs #-}
import Control.Category
import Prelude hiding ((.), id)


{- 
class Category cat where
  id :: cat a a 
  (.) :: cat b c -> cat a b -> cat a c
-}

data Accum a b where
  Accum :: s -> Accum a b

-- | We can pass the outputs of one 'Accum' as the inputs of the next.
instance Category Accum where
  Accum  i1 . Accum  i2 = Accum  (i1, i2)
