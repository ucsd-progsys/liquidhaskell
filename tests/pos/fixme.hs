module ListSort where

{-@ type OList a = [a]<{v: a | (v >= fld)}> @-}

{-@ app :: k:a -> OList {v:a | v < k} -> OList {v:a | v >= k} -> OList a @-}
app :: a -> [a] -> [a] -> [a]
app = error "HOLE"
-- app k []     ys = k:ys
-- app k (x:xs) ys = x:(app k xs ys) 

{- qsort :: (Ord a) => xs:[a] -> OList a @-}
-- qsort []     = []
-- qsort (x:xs) = app x (qsort [y | y <- xs, y < x]) (qsort [z | z <- xs, z >= x]) 
-- qsort (x:xs) = app x (qsort [y | y <- xs, y < x]) (qsort [z | z <- xs, z >= x]) 

{-@ quicksort :: (Ord a) => xs:[a] -> OList a @-}
quicksort []     = []
quicksort (x:xs) = app x xsle xsge
  where xsle = quicksort (takeL x xs)
        xsge = quicksort (takeGE x xs)

{- takeL :: (Ord a) => x:a -> xs:[a] -> [{v:a | v < x}] @-}
takeL :: (Ord a) => a -> [a] -> [a]
-- takeL = error "HOLE"
takeL x []     = []
takeL x (y:ys) = if (y<x) then y:(takeL x ys) else takeL x ys

{- takeGE :: (Ord a) => x:a -> xs:[a] -> [{v:a | v >= x}] @-}
takeGE :: (Ord a) => a -> [a] -> [a]
-- takeGE = error "HOLE"
takeGE x []     = []
takeGE x (y:ys) = if (y>=x) then y:(takeGE x ys) else takeGE x ys


