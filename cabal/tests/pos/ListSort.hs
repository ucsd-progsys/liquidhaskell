module ListSort (insertSort, insertSort', mergeSort, quickSort) where

{-@ type SortedList a = [a]<{v: a | (v >= fld)}> @-}

------------------------------------------------------------------------------
-- Insert Sort ---------------------------------------------------------------
------------------------------------------------------------------------------

{- assert insertSort :: (Ord a) => xs:[a] -> {v: [a]<{v: a | (v >= fld)}> | len(v) = len(xs)} @-}

{-@ assert insertSort :: (Ord a) => xs:[a] -> SortedList a @-}
insertSort            :: (Ord a) => [a] -> [a]
insertSort []         = []
insertSort (x:xs)     = insert x (insertSort xs) 

{-@ assert insertSort' :: (Ord a) => xs:[a] -> SortedList a @-}
insertSort' xs        = foldr insert [] xs

{- assert insert      :: (Ord a) => x:a -> xs: [a]<{v: a | (v >= fld)}> -> {v: [a]<{v: a | (v >= fld)}> | len(v) = (1 + len(xs)) } @-}
insert y []                   = [y]
insert y (x : xs) | y <= x    = y : x : xs 
                  | otherwise = x : insert y xs

------------------------------------------------------------------------------
-- Merge Sort ----------------------------------------------------------------
------------------------------------------------------------------------------

{-@ assert mergeSort :: (Ord a) => xs:[a] -> [a]<{v: a | (v >= fld)}>  @-}
mergeSort :: Ord a => [a] -> [a]
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort xs1) (mergeSort xs2) where (xs1, xs2) = split xs

split :: [a] -> ([a], [a])
split (x:(y:zs)) = (x:xs, y:ys) where (xs, ys) = split zs
split xs         = (xs, [])

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
  | x <= y
  = x:(merge xs (y:ys))
  | otherwise 
  = y:(merge (x:xs) ys)

------------------------------------------------------------------------------
-- Quick Sort ----------------------------------------------------------------
------------------------------------------------------------------------------

{-@ assert quickSort :: (Ord a) => xs:[a] -> [a]<{v: a | (v >= fld)}>  @-}
quickSort []     = []
quickSort (x:xs) = app x (quickSort [y | y <- xs, y < x]) (quickSort [z | z <- xs, z >= x]) 

app k []     ys = k : ys
app k (x:xs) ys = x : app k xs ys



