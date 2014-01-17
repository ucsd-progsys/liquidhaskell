module Concat () where

import Language.Haskell.Liquid.Prelude

------------------------------------------------------------
------------ Longer Version of neg/polypred.hs -------------
------------------------------------------------------------

foo :: [[Int]]
foo = [[choose 1], [choose 2]]

-- concatmap f ls = concat $ map f ls

myconcat []     = []
myconcat (x:xs) = x ++ (myconcat xs) 


myconcat1 :: a -> [[Int]] -> [Int]
myconcat1 _ []     = []
myconcat1 f (x:xs) = x ++ (myconcat1 f xs) 

concat1 f = concat
myconcat2 f = myconcat

r :: Int
r = 5

prop x = liquidAssertB (x == r)

-- ok 
-- propC0 = map prop $ myconcat foo
-- this is safe
-- propC1 = map prop $ myconcat foo
-- propC2 = map prop $ concat foo
-- propC3 = map prop $ concat1 id foo

propC4 = map prop $ myconcat1 id foo

