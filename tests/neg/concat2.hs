module Concat () where

import Language.Haskell.Liquid.Prelude

foo :: [Int]
foo = [choose 1, choose 2]

-- myconcat1 :: (a -> a) -> [[Int]] -> [Int] 
-- :: a goes to False -> safe
myconcat1 :: (a -> [(k,v)]) -> [a] -> [(k, v)]
myconcat1 _ []     = []
myconcat1 f (x:xs) = (f x) ++ (myconcat1 f xs) 

r :: Int
r = 5

prop (x, y) = liquidAssertB (x > r)
--  where r = 5
-- this is safe
propC = map prop $ myconcat1 (\x->[(x, x)]) foo
