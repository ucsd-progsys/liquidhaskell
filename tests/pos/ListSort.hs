module ListSort (insertSort, insertSort', mergeSort, quickSort) where


{-@ type OList a    = [a]<{\fld v -> (v >= fld)}> @-}
{-@ type OListN a N = {v:OList a | len v == N} @-}

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

{-@ mergeSort :: (Ord a) => xs:[a] -> OListN a {len xs} @-}
mergeSort :: Ord a => [a] -> [a]
mergeSort []   = []
mergeSort [x]  = [x]
mergeSort xs   = merge (mergeSort xs1) (mergeSort xs2) 
  where 
    (xs1, xs2) = split xs

{-@ type Half a Xs  = {v:[a] | (len v > 1) => (len v < len Xs)} @-}

{-@ type Halves a Xs = {v: (Half a Xs, Half a Xs) | len (fst v) + len (snd v) == len Xs} @-}
 
{-@ split :: xs:[a] -> Halves a xs @-}
split :: [a] -> ([a], [a])
split (x:(y:zs)) = (x:xs, y:ys) where (xs, ys) = split zs
split xs         = (xs, [])

{-@ merge :: Ord a => xs:OList a -> ys:OList a -> OListN a {len xs + len ys} / [(len xs + len ys)] @-}
merge :: Ord a => [a] -> [a] ->  [a]
merge xs []         = xs
merge [] ys         = ys
merge (x:xs) (y:ys)
  | x <= y          = x: merge xs (y:ys)
  | otherwise       = y : merge (x:xs) ys

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


