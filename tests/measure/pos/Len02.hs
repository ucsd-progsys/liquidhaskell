module Len02 () where

import Language.Haskell.Liquid.Prelude

mylen :: [a] -> Int
mylen []       = 0
mylen (_:xs)   = 1 + mylen xs

mymap :: (a -> b) -> [a] -> [b]
mymap f []     = []
mymap f (x:xs) = (f x) : (mymap f xs)

zs :: [Int]
zs = [1..100]

prop2 :: Bool 
prop2  = liquidAssertB (n1 == n2) 
  where 
    n1 = mylen zs
    n2 = mylen $ mymap (+ 1) zs 
