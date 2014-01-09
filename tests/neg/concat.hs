module Concat () where

import Language.Haskell.Liquid.Prelude

foo :: [Int]
foo = [1..10]

concatmap f ls = concat $ map f ls

myconcatmap f []     = []
myconcatmap f (x:xs) = (f x) ++ (myconcatmap f xs) 


chooseList x = [choose x]
r :: Int
r = 5

prop x = liquidAssertB (x == r)

propMap  = map prop $ myconcatmap chooseList foo
propMap1 = map prop $ concatmap   chooseList foo
