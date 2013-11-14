module spec Data.List where

import GHC.List

assume groupBy :: (a -> a -> GHC.Types.Bool) -> [a] -> [{v:[a] | len(v) > 0}]

assume transpose :: [[a]] -> [{v:[a] | (len v) > 0}]

assume GHC.List.concat :: x:[[a]] -> {v:[a] | (len v) = (sumLens x)}
