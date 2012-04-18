module Test0 where

import Language.Haskell.Liquid.Prelude

getEqs :: Int -> [Int] -> [Int]
getEqs x ys = filter (x ==) ys 

xs :: [Int]
xs = [1,2,3,4,5,6]
--xs = [1]

prop_abs = map (\z -> assert (z >= 0)) ys
             where ys = getEqs 5 xs
