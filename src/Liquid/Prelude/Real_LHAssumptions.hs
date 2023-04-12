module Liquid.Prelude.Real_LHAssumptions where

import GHC.Num()

{-@
assume GHC.Num.* :: (GHC.Num.Num a) => x:a -> y:a -> {v:a | v = x * y} 
@-}
