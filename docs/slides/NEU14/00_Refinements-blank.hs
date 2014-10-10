{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--no-termination" @-}

module Refinements where

import Prelude hiding (map, foldr, foldr1)


-----------------------------------------------------------------------
-- | 1. Simple Refinement Types
-----------------------------------------------------------------------

-- Nat


-- Pos


-----------------------------------------------------------------------
-- | 2. Function Contracts: Preconditions & Dead Code 
-----------------------------------------------------------------------


dead :: String -> a
dead = undefined

-----------------------------------------------------------------------
-- | 3. Function Contracts: Safe Division 
-----------------------------------------------------------------------

divide :: Int -> Int -> Int
divide = undefined




-----------------------------------------------------------------------
-- | 4. Dividing Safely
-----------------------------------------------------------------------

foo     :: Int -> Int -> Int
foo x y = divide x y



-----------------------------------------------------------------------
-- | 4. Data Types
-----------------------------------------------------------------------

-- data List a =

-- infixr 9 `C`



 
-----------------------------------------------------------------------
-- | 4. A few Higher-Order Functions
-----------------------------------------------------------------------

-- map 



-- foldr



-- foldr1





-----------------------------------------------------------------------
-- | 5. Measuring the Size of Data
-----------------------------------------------------------------------

-- measure size




-- measures = strengthened constructors




-- data List a where
--   N :: ...
--   C :: ...




-----------------------------------------------------------------------
-- | 5. Weighted-Averages 
-----------------------------------------------------------------------

-- wtAverage :: List (Int, Int) -> Int








-- Exercise: How would you modify the types to get output `Pos` above? 





-----------------------------------------------------------------------
-- | 5. Ordered Lists: Take 1
-----------------------------------------------------------------------

-- You can do a lot with strengthened constructors


-- Ordered Lists

-- data List a = ...


okList = undefined





-----------------------------------------------------------------------
-- | 6. Sorting Lists 
-----------------------------------------------------------------------


insert     = undefined



insertSort = undefined

















-- Note that adding ordering BREAKS `map`, but ...


