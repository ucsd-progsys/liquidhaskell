module Vec0 () where

import Language.Haskell.Liquid.Prelude
-- import Data.List
import Data.Vector hiding (map, concat, zipWith, filter, foldr, foldl, (++))

propVec = (vs ! 3) == 3
  where xs    = [1,2,3,4] :: [Int]
        vs    = fromList xs
        

