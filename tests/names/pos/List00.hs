-- | The `GHC.TypeLits` seems to royally mess up name resolution.

module MatchIdxs where

import GHC.TypeLits

{-@ zoo :: [a] @-}
zoo :: [a] 
zoo = [] 

