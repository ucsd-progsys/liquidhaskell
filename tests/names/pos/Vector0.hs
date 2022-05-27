-- TAG: names 

module Vector0 where

-- import Language.Haskell.Liquid.Prelude

import Data.Vector hiding (map, concat, zipWith, filter, foldl, foldr, (++))
import qualified Data.Vector

{-@ prop :: [TT] @-}
prop      = [prop0, prop1, prop2, prop3, prop4]
  where
    xs    = [1,2,3,4] :: [Int]
    vs    = fromList xs
    x     = Prelude.head xs
    n     = Prelude.length xs
    prop0 = (x >= 0)
    prop1 = (n > 0)
    prop2 = (Data.Vector.length vs > 0)
    prop3 = (Data.Vector.length vs > 3)
    prop4 = ((vs ! 0 + vs ! 1 + vs ! 2 + vs ! 3) > 0)
