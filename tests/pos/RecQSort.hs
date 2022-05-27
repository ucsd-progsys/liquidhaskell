-- TAG: abref 

module RecQSort (qsort) where

{-@ type OList a =  [a]<{\fld v -> (v >= fld)}>  @-}

{-@ assert sort3 :: (Ord a) => [a] -> OList a @-}
sort3 :: (Ord a) => [a] -> [a]
sort3 = qsort 


qsort:: (Ord a) => [a] -> [a]
{-@ qsort:: (Ord a) => xs:[a] -> OList a / [(len xs), 0]@-}
qsort []     = []
qsort (x:xs) = qpart x xs [] []

qpart  :: (Ord a) => a -> [a] -> [a] -> [a] -> [a]
{-@ qpart  :: (Ord a) => x:a -> q:[a] -> r:[{v:a | (v < x)}] -> p:[{v:a |(v >= x)}] -> OList a / [((len p) + (len r) + (len q)), ((len q) + 1)]@-}
qpart x [] rlt rge =
    app x (qsort rlt) (x:qsort rge)
qpart x (y:ys) rlt rge =
    case compare x y of
        GT -> qpart x ys (y:rlt) rge
        _  -> qpart x ys rlt (y:rge)


{-@ app :: Ord a => x:a -> (OList ({v:a | v < x})) -> (OList ({v:a| v >= x})) -> OList a @-} 
app :: Ord a => a -> [a] -> [a] -> [a]
app k []     ys = ys
app k (x:xs) ys = x : (app k xs ys)

