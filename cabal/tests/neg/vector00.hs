module Vec0 where

import Language.Haskell.Liquid.Prelude

import Data.Vector hiding (map, concat, zipWith, filter, foldr, foldl)
-- {-# ANN module "spec   $LIQUIDHS/Vector.spec" #-}
-- {-# ANN module "spec   $LIQUIDHS/List.spec" #-}
-- {-# ANN module "hquals $LIQUIDHS/List.hquals" #-}

xs    = [1,2,3,4] :: [Int]
vs    = fromList xs
jhala = vs ! 10
