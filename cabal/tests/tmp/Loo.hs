module Loo where

import qualified Goo as G

plusThree = G.plusOne . G.plusTwo
plusFour  = G.plusTwo . G.plusTwo
