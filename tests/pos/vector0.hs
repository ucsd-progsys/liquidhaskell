module Vec0 () where

import Language.Haskell.Liquid.Prelude
import Data.Vector hiding (map, concat, zipWith, filter, foldl, foldr, (++))

prop = prop0 && prop1 && prop2 && prop3 && prop4
  where 
    xs    = [1,2,3,4] :: [Int]
    vs    = fromList xs
    x     = Prelude.head xs
    n     = Prelude.length xs
    prop0 = liquidAssertB (x >= 0)
    prop1 = liquidAssertB (n > 0)
    prop2 = liquidAssertB (Data.Vector.length vs > 0)
    prop3 = liquidAssertB (Data.Vector.length vs > 3)
    prop4 = liquidAssertB ((vs ! 0 + vs ! 1 + vs ! 2 + vs ! 3) > 0)

