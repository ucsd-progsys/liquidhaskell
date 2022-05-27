module Test00c () where

import Language.Haskell.Liquid.Prelude

getEqs x ys = filter (x ==) ys 

xs :: [Int]
xs = [1, 2, 3, 4, 5, 6]

prop_abs = map (\z -> liquidAssertB (z >= 0)) ys
             where ys = getEqs 5 xs
