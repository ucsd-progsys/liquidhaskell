module Loo where

import qualified Goo as G

plusThree = G.plusOne . G.plusTwo
plusFour  = G.plusTwo . G.plusTwo

{-@ assert pp :: z:Int -> {v:Int| v > z} @-}
pp x      = G.plusOne (G.plusOne x)


($$$) x  = x + 1
