{--! run liquid with no-termination -}

module ListSort (insertSort, mergeSort, quickSort) where

-- Verification of sorting algorithms

-- | Describing Sorted Lists

-- The list type is refined with an abstract refinement:
-- data [a] <p :: a -> a -> Prop> where
--   | []  :: [a] <p>
--   | (:) :: h:a -> [a<p h>]<p> -> [a]<p>

-- A sorted list is defined by instantiating 
-- the abstract refinement `p` with `\hd v -> v >= hd`

{-@ type SList a = [a]<{\elt v -> (v >= elt)}> @-}


-- | Insert Sort

insert :: Ord a => a -> [a] -> [a]
insert y []       = [y]
insert y (x : xs) | y <= x    = y : x : xs
                  | otherwise = x : insert y xs

{-@ insertSort :: (Ord a) => xs:[a] -> SList a @-}
insertSort     :: (Ord a) => [a] -> [a]
insertSort     = foldr insert []

-- | Merge Sort

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) | x <= y    = x:(merge xs (y:ys))
                    | otherwise = y:(merge (x:xs) ys)

-- LiquidHaskell can prove that if both arguments of `merge` are sorted lists,
-- then its result is also a sorted list.


split :: [a] -> ([a], [a])
split (x:(y:zs)) = (x:xs, y:ys) where (xs, ys) = split zs
split xs         = (xs, [])

{-@ mergeSort :: (Ord a) => xs:[a] -> SList a @-}
mergeSort     :: Ord a => [a] -> [a]
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort xs1) (mergeSort xs2) where (xs1, xs2) = split xs


-- The system can prove that the result of `mergeSort` is a sorted list.
-- For the first two cases empty lists or lists with one element can easily proved
-- to be sorted. For the last case, if we assume that `mergeSort`'s result is a
-- sorted list, then `merge` is applied to two sorted lists, thus its result will
-- be also a sorted list.

-- |Quick Sort


{-@ append :: k:a 
           -> SList {v:a | v < k } 
           -> SList {v:a | v >= k } 
           -> SList a @-}
append :: a -> [a] -> [a] -> [a]
append k []     ys  = ys
append k (x:xs) ys  = x : append k xs ys

{-@ quickSort :: (Ord a) => [a] -> SList a @-}
quickSort     :: Ord a => [a] -> [a]
quickSort []     = []
quickSort (x:xs) = append x lts gts
  where lts = quickSort [y | y <- xs, y < x]
        gts = quickSort [z | z <- xs, z >= x]


