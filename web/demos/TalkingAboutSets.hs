{--! run liquid with no-termination -}

module TalkingAboutSets where


import Data.Set hiding (filter, split)
import Prelude  hiding (reverse, filter)

-- | Set Operators
-- measure Set_sng  :: a -> (Set a)                    -- ^ singleton
-- measure Set_cup  :: (Set a) -> (Set a) -> (Set a)   -- ^ union
-- measure Set_cap  :: (Set a) -> (Set a) -> (Set a)   -- ^ intersection
-- measure Set_dif  :: (Set a) -> (Set a) -> (Set a)   -- ^ difference

-- | Set Predicates
-- measure Set_emp  :: (Set a) -> Prop                 -- ^ emptiness
-- measure Set_mem  :: a -> (Set a) -> Prop            -- ^ membership
-- measure Set_sub  :: (Set a) -> (Set a) -> Prop      -- ^ inclusion


-- | Talking about Sets (In Code)

-- Data.Set.empty     :: {v:(Set a) | (Set_emp v)}
-- Data.Set.singleton :: x:a -> {v:(Set a) | v = (Set_sng x)}
-- Data.Set.insert :: Ord a => x:a -> xs:(Set a) -> {v:(Set a) | v = (Set_cup xs (Set_sng x))}
-- Data.Set.delete :: Ord a => x:a -> xs:(Set a) -> {v:(Set a) | v = (Set_dif xs (Set_sng x))}
-- Data.Set.union        :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = (Set_cup xs ys)}
-- Data.Set.intersection :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = (Set_cap xs ys)}
-- Data.Set.difference   :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = (Set_dif xs ys)}
-- Data.Set.isSubsetOf :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:Bool | (Prop v) <=> (Set_sub xs ys)}
-- Data.Set.member     :: Ord a => x:a -> xs:(Set a) -> {v:Bool | (Prop v) <=> (Set_mem x xs)}

-- | Proving Theorems With LiquidHaskell

{-@ boolAssert :: {v: Bool | (Prop v)} -> {v:Bool | (Prop v)} @-}
boolAssert True   = True
boolAssert False  = error "boolAssert: False? Never!"


-- | Lets check that `intersection` is commutative ...

{-@ prop_cap_comm :: Set Int -> Set Int -> Bool @-}
prop_cap_comm     :: Set Int -> Set Int -> Bool
prop_cap_comm x y
  = boolAssert
  $ (x `intersection` y) == (y `intersection` x)


-- | that `union` is associative ...

{-@ prop_cup_assoc :: Set Int -> Set Int -> Set Int -> Bool @-}
prop_cup_assoc     :: Set Int -> Set Int -> Set Int -> Bool
prop_cup_assoc x y z
  = boolAssert
  $ (x `union` (y `union` z)) == (x `union` y) `union` z


-- | And that `union` distributes over `intersection`.

{-@ prop_cap_dist :: Set Int -> Set Int -> Set Int -> Bool @-}
prop_cap_dist     :: Set Int -> Set Int -> Set Int -> Bool
prop_cap_dist x y z
  = boolAssert
  $  (x `intersection` (y `union` z))
  == (x `intersection` y) `union` (x `intersection` z)


-- | Of course, while we're at it, lets make sure LiquidHaskell
-- doesn't prove anything thats *not* true ...

{-@ prop_cup_dif_bad :: Set Int -> Set Int -> Bool @-}
prop_cup_dif_bad     :: Set Int -> Set Int -> Bool
prop_cup_dif_bad x y
   = boolAssert
   $ x == (x `union` y) `difference` y

--------------------------------------------------------------------------
-- | The Set of Values in a List -----------------------------------------
--------------------------------------------------------------------------

-- measure listElts :: [a] -> (Set a)
-- listElts ([])    = {v | (? Set_emp(v))}
-- listElts (x:xs)  = {v | v = (Set_cup (Set_sng x) (listElts xs)) }

{-@ predicate SameElts  X Y   = ((listElts X) = (listElts Y))                        @-}
{-@ predicate SubElts   X Y   = (Set_sub (listElts X) (listElts Y))                   @-}
{-@ predicate UnionElts X Y Z = ((listElts X) = (Set_cup (listElts Y) (listElts Z))) @-}


-- | A Trivial Identity

{-@ listId    :: xs:[a] -> {v:[a]| (SameElts v xs)} @-}
listId []     = []
listId (x:xs) = x : listId xs


-- | A Less Trivial Identity: reverse

{-@ reverse       :: xs:[a] -> {v:[a]| (SameElts v xs)} @-}
reverse           = go []
  where
    go acc []     = acc
    go acc (y:ys) = go (y:acc) ys

-- | Appending Lists

{-@ append       :: xs:[a] -> ys:[a] -> {v:[a] | (UnionElts v xs ys) } @-}
append []     ys = ys
append (x:xs) ys = x : append xs ys


-- | Filtering Lists

{-@ filter      :: (a -> Bool) -> xs:[a] -> {v:[a]| (SubElts v xs)} @-}
filter f []     = []
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   = filter f xs


--------------------------------------------------------------------------
-- Merge Sort ------------------------------------------------------------
--------------------------------------------------------------------------

-- | Split

{-@ split    :: xs:[a] -> ([a], [a])<{\ys zs -> (UnionElts xs ys zs)}> @-}

split []     = ([], [])
split (x:xs) = (x:zs, ys)
  where
    (ys, zs) = split xs

-- | Merge

{-@ merge           :: (Ord a) => x:[a] -> y:[a] -> {v:[a] | (UnionElts v x y)} @-}

merge xs []         = xs
merge [] ys         = ys
merge (x:xs) (y:ys)
  | x <= y          = x : merge xs (y:ys)
  | otherwise       = y : merge (x:xs) ys

-- | Merge Sort

{-@ mergeSort :: (Ord a) => xs:[a] -> {v:[a] | (SameElts v xs)} @-}
mergeSort []  = []
mergeSort [x] = [x] 
mergeSort xs  = merge (mergeSort ys) (mergeSort zs)
  where
    (ys, zs)  = split xs

-- Btw, try commenting the "middle case" of mergeSort out. What happens?

