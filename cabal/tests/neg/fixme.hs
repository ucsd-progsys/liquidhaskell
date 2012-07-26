module Concat where

import Language.Haskell.Liquid.Prelude

foo :: [[Int]]
foo = [[1], [2,2]]

r :: Int
r = 5

prop x = liquidAssert (x == r)

myconcat0 :: [[Int]] -> [Int]
myconcat0 []     = []
myconcat0 (x:xs) = x ++ (myconcat0 xs) 

propC4 = map prop $ myconcat0 foo

-- myconcat1 :: a -> [[Int]] -> [Int]
-- myconcat1 _ []     = []
-- myconcat1 f (x:xs) = x ++ (myconcat1 f xs) 

-- propC4 = map prop $ myconcat1 id foo
