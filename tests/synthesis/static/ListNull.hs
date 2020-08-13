{-@ LIQUID "--typed-holes" @-}

module ListNull where

import Language.Haskell.Liquid.Synthesize.Error

{-@ true :: { v: Bool | v } @-}
true :: Bool
true = True

{-@ false :: {v: Bool | not v} @-}
false :: Bool
false = False

{-@ isNull :: xs: [a] -> { v: Bool | (len xs == 0) <=> v } @-}
isNull :: [a] -> Bool
isNull x_S0 =
    case x_S0 of
        [] -> true
        (:) x_Sc x_Sd -> false