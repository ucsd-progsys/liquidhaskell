-- | The `GHC.TypeLits` seems to royally mess up name resolution.

module List00 where

import GHC.TypeLits

{-@ zoo :: [Int] @-}
zoo :: [Int] 
zoo = [] 

