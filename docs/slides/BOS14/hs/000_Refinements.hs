{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--no-termination" @-}

module Refinements where

import Prelude hiding (map, foldr, foldr1)

divide    :: Int -> Int -> Int


-----------------------------------------------------------------------
-- | 1. Simple Refinement Types
-----------------------------------------------------------------------

{-@ type Nat     = {v:Int | v >= 0} @-}
{-@ type Pos     = {v:Int | v >  0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}

{-@ six :: Pos @-}
six = 10 :: Int

-----------------------------------------------------------------------
-- | 2. Function Contracts: Preconditions & Dead Code 
-----------------------------------------------------------------------

{-@ dead :: {v:_ | false} -> a @-}
dead msg = error msg

-----------------------------------------------------------------------
-- | 3. Function Contracts: Safe Division 
-----------------------------------------------------------------------


{-@ divide :: Int -> NonZero -> Int @-}
divide x 0 = dead "divide-by-zero"
divide x n = x `div` n




avg2 x y   = divide (x+y) 2
avg3 x y z = divide (x+y+z) 3


-----------------------------------------------------------------------
-- | But whats the problem here?
-----------------------------------------------------------------------

avg xs     = divide total n
  where
    total  = sum xs
    n      = length xs
