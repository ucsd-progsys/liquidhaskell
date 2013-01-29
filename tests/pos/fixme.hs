module Foo where

import Language.Haskell.Liquid.Prelude

gpp :: [Int] -> [Int]
gpp [] = []
gpp (x:xs) = liquidAssert (x>=0) x : gpp xs


xs :: [Int]
xs = [0..]
ys = gpp xs
