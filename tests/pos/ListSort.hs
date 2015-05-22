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
insertSort'           :: (Ord a) => [a] -> [a]
insertSort' xs        = foldr insert [] xs

insert y []                   = [y]
insert y (x : xs) | y <= x    = y : x : xs 
                  | otherwise = x : insert y xs

------------------------------------------------------------------------------
-- Merge Sort ----------------------------------------------------------------
------------------------------------------------------------------------------

{-@ mergeSort :: (Ord a) => xs:[a] -> {v:OList a| (len v) = (len xs)} @-}
mergeSort :: Ord a => [a] -> [a]
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort xs1) (mergeSort xs2) d 
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

{-@ Decrease merge 4 @-}
{-@ merge :: Ord a => xs:(OList a) -> ys:(OList a) -> d:{v:Int| v = (len xs) + (len ys)} -> {v:(OList a) | (len v) = d} @-}
merge :: Ord a => [a] -> [a] -> Int -> [a]
merge xs [] _ = xs
merge [] ys _ = ys
merge (x:xs) (y:ys) d
  | x <= y
  = x: merge xs (y:ys) (d-1)
  | otherwise 
  = y : merge (x:xs) ys (d-1)

------------------------------------------------------------------------------
-- Quick Sort ----------------------------------------------------------------
------------------------------------------------------------------------------

{-@ quickSort :: (Ord a) => [a] -> OList a @-}
quickSort []     = []
quickSort (x:xs) = append x lts gts 
  where 
    lts          = quickSort [y | y <- xs, y < x]
    gts          = quickSort [z | z <- xs, z >= x]

append k []     ys  = k : ys
append k (x:xs) ys  = x : append k xs ys


