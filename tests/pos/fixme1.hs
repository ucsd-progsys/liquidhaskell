module Foo where

import Language.Haskell.Liquid.Prelude

gpp :: [Int] -> [Int]
gpp [] = []
gpp (x:xs) = liquidAssert (x>=0) x : gpp xs

decr x = x : decr (x-1)
xs :: [Int]
xs = decr 0
ys = gpp xs
