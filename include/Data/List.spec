module spec Data.List where

import GHC.Base
import GHC.List
import GHC.Types

assume groupBy :: (a -> a -> GHC.Types.Bool) -> [a] -> [{v:[a] | len(v) > 0}]

// assume transpose :: [[a]] -> [{v:[a] | 0 < len v}]

insert :: a -> xs:[a] -> {v:[a] | len v == len xs + 1 }

tails :: xs:[a] -> {v:[[a]] | len v == len xs + 1 }
