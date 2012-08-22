module Test where

{-@ type OList a = [a]<{v: a | (v >= fld)}> @-}


{-@ filterGt :: (Ord a) => Maybe a -> OList a -> OList a @-}
filterGt ::  Ord a => Maybe a -> [a] -> [a]
filterGt Nothing  xs = xs
filterGt (Just x) xs = filter' x xs
  where filter' _  []     = [] 
        filter' b' (x:xs) = 
          case compare b' x of LT -> x : (filter' b' xs)
                               EQ -> xs 
                               GT -> filter' b' xs 
