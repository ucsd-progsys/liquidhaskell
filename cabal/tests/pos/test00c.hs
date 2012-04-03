module Test0 where

import Language.Haskell.Liquid.Prelude

myfilter p (x:xs) = if p x then (x:(myfilter p xs)) else myfilter p xs
myfilter p []    = []
getEqs x ys = myfilter (x ==) ys 

xs :: [Int]
xs = [1,2,3,4,5,6]

prop_abs = map (\z -> assert (z >= 0)) ys
             where ys = getEqs 5 xs
