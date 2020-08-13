{-@ LIQUID "--typed-holes" @-}

module Append where

import Language.Haskell.Liquid.Synthesize.Error

{-@ append :: xs: [a] -> ys: [a] -> { v: [a] | len v == len xs + len ys } @-}
append :: [a] -> [a] -> [a]
append x_S0 x_S1 =
    case x_S0 of
        [] -> x_S1
        (:) x_So x_Sp -> append x_Sp ((:) x_So x_S1)
