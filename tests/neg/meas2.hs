module Meas () where

import Language.Haskell.Liquid.Prelude

goo :: a -> Int
goo _ = 1

bob :: [a] -> Int
--bob [] = 0
--bob (n:ns) = goo ns 
bob ms = case ms of 
           []     -> 0
           (n:ns) -> goo ns 

zs :: [Int]
zs = [1..100]

prop2 = liquidAssertB (n2 `eq` 0) 
  where n2 = bob zs
