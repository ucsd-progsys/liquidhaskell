module spec Data.List where

import GHC.Base
import GHC.List
import GHC.Types

assume groupBy :: (a -> a -> GHC.Types.Bool) -> [a] -> [{v:[a] | len(v) > 0}]

assume transpose :: [[a]] -> [{v:[a] | (len v) > 0}]

assume GHC.List.concat :: x:[[a]] -> {v:[a] | (len v) = (sumLens x)}

// qualif SumLensEq(v:List List a, x:List List a): (sumLens v) = (sumLens x)
// qualif SumLensEq(v:List List a, x:List a): (sumLens v) = (len x)
// qualif SumLensLe(v:List List a, x:List List a): (sumLens v) <= (sumLens x)


