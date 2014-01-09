module Vec0 () where

import Language.Haskell.Liquid.Prelude

import Data.Vector hiding (map, concat, zipWith, filter, foldr, foldl, (++))

xs    = [1,2,3,4] :: [Int]
vs    = fromList xs
jhala = vs ! (x + y + z)
  where x = 2
        y = 3
        z = 5
