-- | some fruity test to check reflection of foreign functions with data selectors
-- | in the case of diamond-shaped imports (06A is the top level, 06B and 06C are
-- | the imports using a common original import from 06D)

{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--reflection" @-}

module ReflExt06A where

import ReflExt06D
import ReflExt06B
import ReflExt06C

{-@ reflect calories3 @-}
calories3 :: Fruit -> Int
calories3 fruit = calories1 fruit + calories2 fruit

-- calories 3 = calories1 + calories2 = 4 + 5 = 9 (= 2 * calories + 3)
{-@ lemma :: {calories3 (Banana 3) == 9} @-}
lemma = ()