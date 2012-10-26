module ListSort where

{-@ type OList a = [a]<{v: a | (v >= fld)}> @-}

{-@ app :: k:a -> OList {v:a | v < k} -> OList {v:a | v >= k} -> OList a @-}
app :: a -> [a] -> [a] -> [a]
app = error "HOLE"

{-@ takeL :: (Ord a) => x:a -> xs:[a] -> [{v:a | v < x}] @-}
takeL :: (Ord a) => a -> [a] -> [a]
takeL = error "HOLE"
-- takeL x []     = []
-- takeL x (y:ys) = if (y<x) then y:(takeL x ys) else takeL x ys


{-@ quicksort :: (Ord a) => xs:[a] -> OList a @-}
quicksort []     = []
quicksort (x:xs) = app x xsle xsge
  where xsle = quicksort (takeL x xs)
        xsge = quicksort (takeGE x xs)

{- takeGE :: (Ord a) => x:a -> xs:[a] -> [{v:a | v >= x}] @-}
takeGE x []     = []
takeGE x (y:ysXXX) = if (y>=x) then y:(takeGE x ysXXX) else takeGE x ysXXX


