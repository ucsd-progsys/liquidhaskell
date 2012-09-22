module Test where

{-@ type OList a = [a]<{v: a | (v >= fld)}> @-}

{-@ filterGt :: (Ord a) => Maybe a -> OList a -> OList a @-}

filterGt ::  Ord a => Maybe a -> [a] -> [a]
filterGt Nothing  xs = xs
filterGt (Just x) xs = filter' x xs
-- The following works fine, because toplevel recs go through TXREC?
-- filterGt (Just x) xs = filter'' x xs
  where filter' _  []     = [] 
        filter' b' (x:xs) = case compare b' x of 
                              GT -> x : filter' b' xs 
                              LT -> x:xs 
                              EQ -> xs 

filter'' _  []     = [] 
filter'' b' (x:xs) = case compare b' x of 
                      GT -> x : filter'' b' xs 
                      LT -> x:xs 
                      EQ -> xs 




-- {- filter' :: (Ord a) => a -> OList a -> OList a @-}
