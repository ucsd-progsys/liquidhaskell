module Vec0 () where

import Language.Haskell.Liquid.Prelude

import Data.Vector hiding(map, concat, zipWith, filter, foldl, foldr, (++))

xs  = [1,2,3,4] :: [Int]
vs  = fromList xs

--prop0 = liquidAssertB (x >= 0)
--        where x = Prelude.head xs
--
--prop1 = liquidAssertB (n > 0)
--        where n = Prelude.length xs
--
--prop2 = liquidAssertB (Data.Vector.length vs > 0)
--prop3 = liquidAssertB (Data.Vector.length vs > 3)

prop6 = crash (0 == 1) 
x0    = vs ! 0
