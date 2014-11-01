{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--no-termination" @-}

module Refinements where

import Prelude hiding (map, foldr, foldr1)


-----------------------------------------------------------------------
-- | 1. Simple Refinement Types
-----------------------------------------------------------------------

-- Nat
{-@ type Nat = {v: Int | v >= 0} @-}

-- Pos
{-@ type Pos = {v: Int | v > 0} @-}


-----------------------------------------------------------------------
-- | 2. Function Contracts: Preconditions & Dead Code 
-----------------------------------------------------------------------


{-@ dead :: {v:String | false} -> a @-}
dead :: String -> a 
dead = undefined

-----------------------------------------------------------------------
-- | 3. Function Contracts: Safe Division 
-----------------------------------------------------------------------

{-@ divide :: Int -> Pos -> Int @-}
divide :: Int -> Int -> Int
divide n 0 = dead "dbz"
divide n k = n `div` k




-----------------------------------------------------------------------
-- | 4. Dividing Safely
-----------------------------------------------------------------------

{-@ foo :: Int -> Nat -> Int @-}
foo     :: Int -> Int -> Int
foo x y = if y == 0 then foo x y else divide x y



-----------------------------------------------------------------------
-- | 4. Data Types
-----------------------------------------------------------------------

data List a = N | C a (List a)

infixr 9 `C`



 
-----------------------------------------------------------------------
-- | 4. A few Higher-Order Functions
-----------------------------------------------------------------------

{-@ map :: (a -> b) -> xs:_ -> {v:_ | size v = size xs} @-}
map f N = N
map f (C x xs) = f x `C` (map f xs)



-- foldr
foldr f b N        = b
foldr f b (C x xs) = f x (foldr f b xs)

-- foldr1
{-@ foldr1 :: (a -> a -> a) -> {v:List a | size v > 0} -> a @-}
foldr1 f (C x xs) = foldr f x xs
foldr1 _ N        = dead "EMPTY!!!"





-----------------------------------------------------------------------
-- | 5. Measuring the Size of Data
-----------------------------------------------------------------------

{-@ measure size @-}
size :: List a -> Int
size N        = 0
size (C x xs) = 1 + size xs 



-- measures = strengthened constructors




-- data List a where
--   N :: forall a. {List a | size v = 0}...
--   C :: forall a. x:a -> xs:List a -> {v:List a | size v = 1 + size xs}




-----------------------------------------------------------------------
-- | 5. Weighted-Averages 
-----------------------------------------------------------------------


{-@ wtAverage :: {v:List (Pos, Int) | size v > 0} -> Int @-}
wtAverage :: List (Int, Int) -> Int
wtAverage wxs = total `divide` weights
  where
    total     = foldr1 (+) (map (\(w,x) -> w * x) wxs) 
    weights   = foldr1 (+) (map (\(w,_) -> w)     wxs) 
    






-- Exercise: How would you modify the types to get output `Pos` above? 





-----------------------------------------------------------------------
-- | 5. Ordered Lists: Take 1
-----------------------------------------------------------------------

-- You can do a lot with strengthened constructors


-- Ordered Lists


{-@ data List a = N | C {x :: a, xs :: List {v:a | x <= v}} @-}
okList = 1 `C` 2 `C` 4 `C` N





-----------------------------------------------------------------------
-- | 6. Sorting Lists 
-----------------------------------------------------------------------


insert x N        = x `C` N
insert x (C y ys)
  | x < y         = x `C` (y `C` ys)
  | otherwise     = y `C` (insert x ys)


insertSort []     = N
insertSort (x:xs) = insert x (insertSort xs)

















-- Note that adding ordering BREAKS `map`, but ...


