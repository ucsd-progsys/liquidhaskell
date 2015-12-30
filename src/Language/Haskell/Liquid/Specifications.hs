-- | This module contains the LH specifications (assumes) for 
--   various imported modules.

module Language.Haskell.Liquid.Specifications where

import GHC.Exts 

{-@ type ListNE a = {v:[a] | len v > 0} @-}

{-@ assume GHC.Exts.sortWith :: Ord b => (a -> b) -> xs:[a] -> {v:[a] | len v == len xs} @-}

{-@ assume GHC.Exts.groupWith :: Ord b => (a -> b) -> [a] -> [ListNE a] @-}
