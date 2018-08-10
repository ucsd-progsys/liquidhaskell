module Vec0 (x0, prop0, prop1, prop2, prop3) where

import Language.Haskell.Liquid.Prelude

import Data.Vector hiding (map, concat, zipWith, filter, foldr, foldl, (++))

xs :: [Int]
xs  = [1,2,3,4]

vs :: Vector Int
vs  = fromList xs

prop0 :: Bool
prop0 = liquidAssertB (x >= 0)
        where x = Prelude.head xs

prop1 :: Bool
prop1 = liquidAssertB (n > 0)
        where n = Prelude.length xs

prop2 :: Bool
prop2 = liquidAssertB (Data.Vector.length vs > 0)

prop3 :: Bool
prop3 = liquidAssertB (Data.Vector.length vs > 3)

x0    :: [ Int ]
x0    = [ vs ! 0
        , vs ! 1
        , vs ! 2
        , vs ! 3
        , vs ! 4 ]
