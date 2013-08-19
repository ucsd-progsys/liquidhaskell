module spec Data.List where

import GHC.List

assume groupBy :: (a -> a -> GHC.Types.Bool) -> [a] -> [{v:[a] | len(v) > 0}]

assume transpose :: [[a]] -> [{v:[a] | (len v) > 0}]

assume GHC.List.splitAt :: n:Nat -> x:[a] -> ({v:[a] | (Min (len v) (len x) n)},[a])<{\x1 x2 -> (len x2) = (len x) - (len x1)}>

assume GHC.List.concat :: x:[[a]] -> {v:[a] | (len v) = (sumLens x)}

measure sumLens :: [[a]] -> GHC.Types.Int
sumLens ([])   = 0
sumLens (c:cs) = (len c) + (sumLens cs)

qualif SumLensEq(v:List List a, x:List a): (sumLens v) = (len x)

