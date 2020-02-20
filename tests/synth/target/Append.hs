{-@ LIQUID "--typed-holes" @-}

module Append where

import Language.Haskell.Liquid.Synthesize.Error

{-@ append :: xs: [a] -> ys: [a] -> { v: [a] | len v == len xs + len ys } @-}
append :: [a] -> [a] -> [a]
append = _goal
