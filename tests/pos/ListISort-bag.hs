module ListSort where

import qualified Language.Haskell.Liquid.Bag as B

{-@ type OList a = [a]<{\fld v -> v >= fld}> @-}

{-@ insertSort    :: (Ord a) => xs:[a] -> {v : OList a | bag v = bag xs} @-}
insertSort        :: (Ord a) => [a] -> [a]
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs)

{-@ insert      :: (Ord a) => x:a -> xs: OList a -> {v: OList a | bag v = B.put x (bag xs) } @-}
insert y []     = [y]
insert y (x:xs)
  | y <= x    	= y : x : xs
  | otherwise 	= x : insert y xs

{-@ measure bag @-}
bag :: (Ord a) => [a] -> B.Bag a
bag []     = B.empty
bag (x:xs) = B.put x (bag xs)
