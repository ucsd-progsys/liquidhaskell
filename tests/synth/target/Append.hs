{-@ LIQUID "--typed-holes" @-}

module Append where

{-@ err :: { v: Int | false } -> a @-}
err :: Int -> a
err s = undefined

{-@ append :: xs: [a] -> ys: [a] -> { v: [a] | len v == len xs + len ys } @-}
append :: [a] -> [a] -> [a]
append = _goal
