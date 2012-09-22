module spec Data.List where

import GHC.List

assume groupBy :: (a -> a -> Bool) -> [a] -> [{v:[a] | len(v) > 0}] 
