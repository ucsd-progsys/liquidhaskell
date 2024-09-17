-- | some fruity test to check reflection of foreign functions with data selectors
-- | in the case of diamond-shaped imports (06A is the top level, 06B and 06C are
-- | the imports using a common original import from 06D)

-- Note: this pragma is needed so that the unfoldings end up in the
-- interface files, even with `-O0`
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module ReflExt06D where

calories :: Fruit -> Int
calories Apple = 0
calories (Banana i) = i

data Fruit = Apple | Banana Int
