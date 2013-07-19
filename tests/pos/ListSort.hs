module ListSort (insertSort, insertSort', mergeSort, quickSort) where


{-@ type OList a = [a]<{\fld v -> (v >= fld)}> @-}

------------------------------------------------------------------------------
-- Insert Sort ---------------------------------------------------------------
------------------------------------------------------------------------------

{-@ insertSort :: (Ord a) => xs:[a] -> OList a @-}
insertSort            :: (Ord a) => [a] -> [a]
insertSort []         = []
insertSort (x:xs)     = insert x (insertSort xs) 

{-@ insertSort' :: (Ord a) => xs:[a] -> OList a @-}
insertSort' xs        = foldr insert [] xs

insert y []                   = [y]
insert y (x : xs) | y <= x    = y : x : xs 
                  | otherwise = x : insert y xs

------------------------------------------------------------------------------
-- Merge Sort ----------------------------------------------------------------
------------------------------------------------------------------------------

{-@ mergeSort :: (Ord a) => [a] -> OList a @-}
mergeSort :: Ord a => [a] -> [a]
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge d (mergeSort xs1) (mergeSort xs2) 
  where (xs1, xs2) = split xs
        d          = length xs

{-@ predicate Pr X Y = (((len Y) > 1) => ((len Y) < (len X))) @-}

{-@ split :: xs:[a] 
          -> ({v:[a] | (Pr xs v)}, {v:[a]|(Pr xs v)})
                 <{\x y -> ((len x) + (len y) = (len xs))}> 
  @-}

split :: [a] -> ([a], [a])
split (x:(y:zs)) = (x:xs, y:ys) where (xs, ys) = split zs
split xs         = (xs, [])

merge :: Ord a => Int -> [a] -> [a] -> [a]
merge _ xs [] = xs
merge _ [] ys = ys
merge d (x:xs) (y:ys)
  | x <= y
  = x:(merge (d-1) xs (y:ys))
  | otherwise 
  = y:(merge (d-1) (x:xs) ys)

------------------------------------------------------------------------------
-- Quick Sort ----------------------------------------------------------------
------------------------------------------------------------------------------

{-@ quickSort :: (Ord a) => [a] -> OList a @-}
quickSort []     = []
quickSort (x:xs) = append x lts gts 
  where lts = quickSort [y | y <- xs, y < x]
        gts = quickSort [z | z <- xs, z >= x]

append k []     ys  = k : ys
append k (x:xs) ys  = x : append k xs ys






