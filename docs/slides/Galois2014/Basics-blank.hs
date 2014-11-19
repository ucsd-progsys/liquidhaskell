{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--smtsolver=cvc4" @-}
module Basics where
import Prelude hiding (map,foldr,foldr1)

-----------------------------------------------------------------------
-- | 1. Simple Refinement Types
-----------------------------------------------------------------------

{-@ six :: {v:Int | v = 6} @-}
six = 6


{-@ type Nat     = {v:Int | v >= 0} @-}
{-@ type Pos     = {v:Int | v >  0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}

{-@ six' :: Pos @-}
six' = six



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

-----------------------------------------------------------------------
-- | 4. Function Contracts: Postconditions
-----------------------------------------------------------------------

{-@ abs :: Int -> Nat @-}
abs x | x >= 0    = x
      | otherwise = 0 - x





{- abs :: x:Int -> {v:Nat | v >= x} @-}



-----------------------------------------------------------------------
-- | 5. Algebraic Datatypes
-----------------------------------------------------------------------

data List a = N | C a (List a)
infixr `C`

{-@ type Rng Lo Hi = {v:Int | v >= Lo && v < Hi} @-}

{-@ list :: List (Rng 0 100) @-}
list = 1 `C` 10 `C` 30 `C` N




{-@ map :: (a -> b) -> xs:_ -> {v:_ | llen v = llen xs} @-}
map f N        = N
map f (C x xs) = f x `C` (map f xs)


-- foldr
foldr f b N        = b
foldr f b (C x xs) = f x (foldr f b xs)

-- foldr1
{-@ foldr1 :: (a -> a -> a) -> {v:List a | llen v > 0} -> a @-}
foldr1 f (C x xs) = foldr f x xs
foldr1 _ N        = dead "EMPTY!!!"





-----------------------------------------------------------------------
-- | 6. Measuring Data
-----------------------------------------------------------------------

{-@ measure llen :: List a -> Int
    llen (N)      = 0
    llen (C x xs) = 1 + (llen xs)
  @-}





{-@ wtAverage :: {v:List (Pos, Int) | llen v > 0} -> Int @-}
wtAverage :: List (Int, Int) -> Int
wtAverage wxs = total `divide` weights
  where
    total     = foldr1 (+) (map (\(w,x) -> w * x) wxs) 
    weights   = foldr1 (+) (map (\(w,_) -> w)     wxs) 










-----------------------------------------------------------------------
-- | 7. Representation Invariants
-----------------------------------------------------------------------

data CSV a = CSV { cols :: [String], rows :: [[a]] }

{-@
data CSV a = CSV { cols :: [String]
                 , rows :: [ListN a (len cols)] }
@-}

{-@ type ListN a N = {v:[a] | len v = N} @-}


csv = CSV [ "Month", "Days"]
          [ ["Jan",  "31"]
          , ["Feb", "28"] 
          ]







-----------------------------------------------------------------------
-- | 8. Type Classes
-----------------------------------------------------------------------

class Indexable f where
  size :: f a -> Int
  at   :: f a -> Int -> a

{-@ class Indexable f where
      size :: forall a. xs:f a -> {v:Nat | v = sz xs}
      at   :: forall a. xs:f a -> {v:Nat | v < sz xs} -> a
  @-}

{-@ class measure sz :: forall a. a -> Int @-}

instance Indexable List where
  size N        = 0
  size (C x xs) = 1 + size xs

  (C x xs) `at` 0 = x
  (C x xs) `at` i = xs `at` (i-1)

{-@ instance measure sz :: List a -> Int
    sz (N)      = 0
    sz (C x xs) = 1 + (sz xs)
  @-}




instance Indexable [] where
  size []        = 0
  size (x:xs)    = 1 + size xs

  (x:xs) `at` 0  = x
  (x:xs) `at` i  = xs `at` (i-1)

{-@ instance measure sz :: [a] -> Int
    sz ([])   = 0
    sz (x:xs) = 1 + (sz xs)
  @-}


sum :: (Indexable f) => f Int -> Int
sum xs = go 0 
  where
    go i | i < size xs = xs `at` i + go (i+1)
         | otherwise   = 0




















-- Local Variables:
-- flycheck-checker: haskell-liquid
-- End:

six :: Int
divide :: Int -> Int -> Int
abs :: Int -> Int
list :: List Int

{-@ invariant {v:[a] | sz v >= 0} @-}
{-@ qualif Sz(v:int, x:a): v = sz x @-}
{-@ qualif Sz(v:int, x:a): v < sz x @-}
