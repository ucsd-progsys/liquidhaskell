module Test where


{-@ type OList a = [a]<{v: a | (v >= fld)}> @-}

{-@ filterGt :: (Ord a) => x:Maybe a -> OList a -> OList {v:a | ((isJust(x)) => (fromJust(x) <= v)) } @-}

filterGt ::  Ord a => Maybe a -> [a] -> [a]
filterGt Nothing  xs = xs
filterGt (Just x) xs = foo x xs
  
{-@ foo :: (Ord a) => z:a -> OList a -> OList {v:a | z <= v} @-}
foo y []     = []
foo y (x:xs) 
 = case compare y x of 
    GT -> foo y xs 
    LT -> x:xs 
    EQ -> xs 
--   | y > x    = foo y xs 
--   | y < x    = x:xs 
--   | y == x   = xs 


