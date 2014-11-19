{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--no-termination" @-}

module Refinements where

import Prelude hiding (abs)

divide    :: Int -> Int -> Int


-----------------------------------------------------------------------
-- | 1. Simple Refinement Types
-----------------------------------------------------------------------

{-@ type Nat     = {v:Int | v >= 0} @-}
{-@ type Pos     = {v:Int | v >  0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}


{-@ six :: NonZero @-}
six = 10 :: Int



-----------------------------------------------------------------------
-- | 2. Function Contracts: Preconditions & Dead Code 
-----------------------------------------------------------------------

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

-- Precondition says, there are **NO** valid inputs for @die@.
-- If program type-checks, means @die@ is **NEVER** called at run-time.





-----------------------------------------------------------------------
-- | 3. Function Contracts: Safe Division 
-----------------------------------------------------------------------

divide x 0 = undefined -- die "divide-by-zero"
divide x n = x `div` n



-- | What's the problem above? Nothing to *prevent*
--   us from calling `divide` with 0. Oops.
--   How shall we fix it?







avg2 x y   = divide (x + y)     2
avg3 x y z = divide (x + y + z) 3









-----------------------------------------------------------------------
-- | But whats the problem here?
-----------------------------------------------------------------------

avg xs     = divide total n 
  where
    total  = sum xs
    n      = length xs



-- | Try to fix the above using `abs`olute values?

abs :: Int -> Int
abs x | x > 0     = x
      | otherwise = 0 - x















--------------------------------------------------------------
-- | CHEAT AREA ----------------------------------------------
--------------------------------------------------------------

-- # START Errors 0
-- # END   Errors 1 (avg)

{- abs    :: x:Int -> {v:Nat | x <= v} @-}
{- divide :: Int -> NonZero -> Int     @-}
