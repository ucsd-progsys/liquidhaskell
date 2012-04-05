module Vec0 where

import Language.Haskell.Liquid.Prelude
import Data.List
import Data.Vector hiding (map, zipWith, filter, foldr, foldl)

xs    = [1,2,3,4] :: [Int]
vs    = fromList xs
jhala = vs ! 3 
