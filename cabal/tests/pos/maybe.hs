module Test where


{-@ type OList a = [a]<{v: a | (v >= fld)}> @-}

{-@ filterGt :: (Ord a) => x:Maybe a -> OList a -> OList {v:a | ((isJust(x)) => (fromJust(x) < v)) } @-}

filterGt ::  Ord a => Maybe a -> [a] -> [a]
filterGt Nothing  xs = xs
filterGt (Just x) xs = filter' x xs
  where filter' _  []     = [] 
        filter' b' (x:xs) = case compare b' x of 
                              GT -> filter' b' xs 
                              LT -> x:xs 
                              EQ -> xs 

