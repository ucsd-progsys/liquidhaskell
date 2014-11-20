{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--no-termination" @-}
{- LIQUID "--smtsolver=cvc4" @-}

module Refinements where

import Prelude hiding (abs)

divide    :: Int -> Int -> Int


-----------------------------------------------------------------------
-- | Simple Refinement Types
-----------------------------------------------------------------------

{-@ six :: {v:Int | v = 6} @-}
six = 6 :: Int



-----------------------------------------------------------------------
-- | Type Aliases are nice, we're gonna be liberal in our use of them
-----------------------------------------------------------------------

{-@ type Nat     = {v:Int | v >= 0} @-}
{-@ type Pos     = {v:Int | v >  0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}


-----------------------------------------------------------------------
-- | Subtyping via Implication
-----------------------------------------------------------------------

{-@ six' :: NonZero @-}
six' = six

-- {v:Int | v = 6} <: {v:Int | v /= 0}
-- ==>
--          v = 6  =>          v /= 0


-----------------------------------------------------------------------
-- | Function Contracts: Preconditions & Dead Code 
-----------------------------------------------------------------------

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

-- Precondition says, there are **NO** valid inputs for @die@.
-- If program type-checks, means @die@ is **NEVER** called at run-time.





-----------------------------------------------------------------------
-- | Function Contracts: Safe Division 
-----------------------------------------------------------------------

divide x 0 = die "divide-by-zero"
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

















--------------------------------------------------------------
-- | CHEAT AREA ----------------------------------------------
--------------------------------------------------------------

-- # START Errors 0
-- # END   Errors 1 (avg)

{- divide :: Int -> NonZero -> Int     @-}
