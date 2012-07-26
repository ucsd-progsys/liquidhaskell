module Vec0 where

import Language.Haskell.Liquid.Prelude
import Data.Vector hiding (map, concat, zipWith, filter, foldr, foldl, (++))

xs  = [1,2,3,4] :: [Int]
vs  = fromList xs

prop0 = liquidAssert (x >= 0)
        where x = Prelude.head xs

prop1 = liquidAssert (n > 0)
        where n = Prelude.length xs

prop2 = liquidAssert (Data.Vector.length vs > 0)
prop3 = liquidAssert (Data.Vector.length vs > 3)

x0    = [ vs ! 0
        , vs ! 1
        , vs ! 2
        , vs ! 3 
        , vs ! 4]
