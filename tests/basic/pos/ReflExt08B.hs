-- | test reflection of a function that is using a datatype, but not in case split alternatives

-- Note: this pragma is needed so that the unfoldings end up in the
-- interface files, even with `-O0`
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module ReflExt08B where

{-# INLINE fromCal #-}
fromCal :: Int -> Fruit
fromCal 0 = Apple
fromCal i = (Banana i)

data Fruit = Apple | Banana Int
