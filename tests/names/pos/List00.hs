-- | The `GHC.TypeLits` seems to royally mess up name resolution.

module MatchIdxs where

import GHC.TypeLits

{-@ zoo :: [Int] @-}
zoo :: [Int] 
zoo = [] 

