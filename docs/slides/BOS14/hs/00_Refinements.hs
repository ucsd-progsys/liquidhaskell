{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--no-termination" @-}

module Refinements where


import Prelude hiding (map, foldr, foldr1)


-- wtAverage :: [(Int, Int)] -> Int

divide    :: Int -> Int -> Int
divide n 0 = dead "div by zero"
divide n k = n `div` k


{-@ dead :: {v:_ | false} -> a @-}
dead msg = error msg


-----------------------------------------------------------------------
-- | 1. Simple Refinement Types
-----------------------------------------------------------------------


{-@ type Nat = {v:Int | v >= 0} @-}
{-@ type Pos = {v:Int | v >  0} @-}


-----------------------------------------------------------------------
-- | 2. Function Contracts: Preconditions & Dead Code 
-----------------------------------------------------------------------

{-@ dead :: {v:_ | false} -> a @-}
dead msg = error msg

-----------------------------------------------------------------------
-- | 3. Function Contracts: Safe Division 
-----------------------------------------------------------------------


{-@ divide :: Int -> Pos -> Int @-}
divide x 0 = dead "divide-by-zero"
divide x n = x `div` n


-----------------------------------------------------------------------
-- | 4. Dividing Safely
-----------------------------------------------------------------------

{-@ foo :: Int -> Nat -> Int @-}
foo x y    = divide x y



-----------------------------------------------------------------------
-- | 4. Data Types
-----------------------------------------------------------------------

data List a = N | C a (List a)

infixr 9 `C`

 
-----------------------------------------------------------------------
-- | 4. Measuring the Size of Data
-----------------------------------------------------------------------

{-@ measure size @-}
size          :: List a -> Int
size (C x xs) = 1 + size xs 
size N        = 0

-- data List a where
--   N :: forall a. {v: List a | size v = 0}
--   C :: forall a. x:a -> xs:List a -> {v: List a | size v = 1 + size xs}
                
-----------------------------------------------------------------------
-- | 5. A few Higher-Order Functions
-----------------------------------------------------------------------

{-@ map              :: (a -> b) -> xs:List a -> {v: List b | size v = size xs} @-}
map f (N)            = N
map f (C x xs)       = C (f x) (map f xs) 

{-@ foldr1           :: (a -> a -> a) -> {v: List a | 0 < size v } -> a @-}
foldr1 f (C x xs)    = foldr f x xs
foldr1 f N           = dead "foldr1"

foldr f acc N        = acc
foldr f acc (C x xs) = f x (foldr f acc xs)
 

-----------------------------------------------------------------------
-- | 5. Weighted-Averages 
-----------------------------------------------------------------------

{-@ wtAverage :: {v : List (Pos, Pos) | size v > 0} -> Int @-}
wtAverage wxs = total `divide` weights
  where
    total     = sum $ map (\(w, x) -> w * x) wxs
    weights   = sum $ map (\(w, _) -> w    ) wxs
    sum       = foldr1 (+)


-- | Exercise: How would you modify the types to get output `Pos` above? 

-----------------------------------------------------------------------
-- | 5. Ordered Lists: Take 1
-----------------------------------------------------------------------

{- data List a = N | C {x :: a, xs :: List {v:a | x <= v}} @-}

okList :: List Int
okList = 1 `C` 2 `C` 4 `C` N

-- Note that adding ordering BREAKS `map`...



{-@ insert         :: _ -> xs:_ -> {v:_ | size v = 1 + size xs} @-}
insert x N         = x `C` N
insert x (C y ys)
  | x <= y         = x `C` y `C` ys
  | otherwise      = y `C` insert x ys 




{-@ insertSort     :: (Ord a) => xs:[a] -> {v:List a | size v = len xs} @-}
insertSort []      = N
insertSort (x:xs)  = insert x (insertSort xs)
