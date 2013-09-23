module GhcSort where

{-@ type OList a =  [a]<{\fld v -> (v >= fld)}>  @-}

{-@ assert sort3 :: (Ord a) => [a] -> OList a @-}
sort3 :: (Ord a) => [a] -> [a]
sort3 ls = qsort ls d 0 
  where d = (length ls) 


{-@ Decrease qsort 3 4 @-}
{-@ Decrease qpart 6 7 @-}
qsort:: (Ord a) => [a] -> Int -> Int -> [a]
{-@ qsort:: (Ord a) => xs:[a] -> {v:Int |v = (len xs)} -> {v:Int | v = 0} -> OList a @-}
qsort []  _ _  = []
qsort (x:xs) _ _ = qpart x xs [] [] d1 d2
  where d1 = (length xs) 
        d2 = (length xs + 1) 

qpart  :: (Ord a) => a -> [a] -> [a] -> [a] -> Int -> Int -> [a]
{-@ qpart  :: (Ord a) => x:a -> q:[a] -> r:[{v:a | ((true) && (v < x))}] -> p:[{v:a | ((true) && (v >= x))}] -> {v:Int | v = ((len r) + (len q) + (len p))} -> {v:Int|v = (len q) + 1} -> OList a @-}
qpart x [] rlt rge _ _ =
    app x (qsort rlt dl 0) (x:qsort rge dg 0)
  where dl = length rlt
        dg = length rge
qpart x (y:ys) rlt rge d1 d2 =
    case compare x y of
        GT -> qpart x ys (y:rlt) rge d1 (d2-1)
        _  -> qpart x ys rlt (y:rge) d1 (d2-1)


{-@ app :: Ord a => x:a -> (OList ({v:a | v < x})) -> (OList ({v:a| v >= x})) -> OList a @-} 
app :: Ord a => a -> [a] -> [a] -> [a]
app k []     ys = ys
app k (x:xs) ys = x : (app k xs ys)

