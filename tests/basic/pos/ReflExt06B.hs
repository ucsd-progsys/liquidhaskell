-- | some fruity test to check reflection of foreign functions with data selectors
-- | in the case of diamond-shaped imports (06A is the top level, 06B and 06C are
-- | the imports using a common original import from 06D)

{-@ LIQUID "--reflection" @-}

module ReflExt06B where

import ReflExt06D

{-@ reflect calories @-}

{-@ reflect calories1 @-}
calories1 :: Fruit -> Int
calories1 fruit = calories fruit + 1