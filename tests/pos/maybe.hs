module Test () where

import Language.Haskell.Liquid.Prelude (liquidAssert)

{-@ type OList a = [a]<{\fld v -> (v >= fld)}> @-}

{-@ filterGt :: (Ord a) => x:Maybe a -> OList a -> OList {v:a | ((isJust(x)) => (fromJust(x) <= v)) } @-}

filterGt ::  Ord a => Maybe a -> [a] -> [a]
filterGt Nothing  xs = xs
filterGt (Just x) xs = foo x xs
  
foo y xs = foo' y xs

foo' :: (Ord a) => a -> [a] -> [a]
foo' y []     = []
foo' y (x:xs) 
 = case compare y x of 
     GT -> foo' y xs 
     LT -> x:xs 
     EQ -> xs 

{-@ bar :: (Ord a) => z:a -> OList a -> OList {v:a | z <= v} @-}
bar y xs = bar' y xs

bar' y []     = []
bar' y (x:xs) 
  | y > x    = bar' y xs 
  | y < x    = x:xs 
  | y == x   = xs 


